//! WI-753 — a rule-body occurrence is BUILT FROM ITS PARSE NODE, not materialized from the
//! hash-consed term it lowered to, so every node is located at its own site.
//!
//! The defect: the rule-body walk handed some nodes to an early return that rebuilt them from
//! the lowered KB term and looked each node's location up in a table keyed by the term's
//! `TermId`. A `TermId` is hash-consed, so two IDENTICAL siblings are ONE key — both were
//! reported at the first one's offset — and a node the table missed fell back to the
//! cross-file, first-write-wins `kb.term_spans`.
//!
//! The probe is the supplier-tie refusal (WI-1012/1035), which is raised AT a rule-body method
//! call and located there: the one diagnostic that reliably reaches a node inside such a call.
//!
//! ## Back-out (measured)
//!
//! Stage 1 — the converter's METHOD CALL (`dot_apply`). With `dot_apply_expr` disconnected in
//! `build_body_atom_occurrence_inner` (the call to it replaced by `None`), the method call takes
//! the early return again and `identical_sibling_calls_are_each_located_at_their_own_site`
//! FAILS: both `get` calls carry the FIRST one's span.
//! `a_single_nested_call_is_located_at_the_call` passes either way BY DESIGN — the per-atom
//! table already located a node with no identical twin (WI-1039); it pins that the native
//! build keeps that.
//!
//! Stage 2 — a REFLECT FORM written as data (`occurrence_term(?e, if_expr(…))`), in both
//! spellings: UNRESOLVED (`import anthill.reflect.Expr` alone — the corpus spelling, built as
//! the generic application) and RESOLVED (`import anthill.reflect.Expr.{if_expr, var_ref}`,
//! built by `entity_ctor_expr`). Backed out by restoring the early return for reflect forms
//! (`} else if written_entity || reflect_form {`, and the `None if written_entity` arm
//! disabled): `identical_reflect_pattern_children_are_each_located_at_their_own_site` FAILS —
//! the two `var_ref(name: a)` branches carry ONE span, the first's (`(166, 166)` for
//! `(166, 197)`); with ONLY the `None if written_entity` arm disabled, it fails on the
//! RESOLVED row alone (`(209, 209)` for `(209, 240)`). `a_reflect_pattern_still_reads_as_its_keyed_form` passes either way BY
//! DESIGN — both carriers take `visit_fn`'s arms — and pins that the native build keeps the
//! reading.
//!
use crate::wi1012_static_supplier_tie_test::{located, refusal};
use crate::wi1026_rule_body_spec_op_dispatch_test::{
    program, TWO_LEAF as OWN, TWO_SUPPLY as RIVAL_FACT,
};

/// The `line:col` of the `nth` (0-based) occurrence of `needle` in `src` — 1-based on both
/// axes, as `load.rs` renders a location. Panics when there are fewer, so a fixture that
/// drifts away from what the test is about fails rather than measuring something else.
fn site(src: &str, needle: &str, nth: usize) -> String {
    let mut seen = 0;
    for (i, line) in src.lines().enumerate() {
        let mut from = 0;
        while let Some(off) = line[from..].find(needle) {
            if seen == nth {
                return format!("{}:{}", i + 1, from + off + 1);
            }
            seen += 1;
            from += off + needle.len();
        }
    }
    panic!("fixture guard: occurrence {nth} of {needle:?} is not in:\n{src}")
}

/// A carrier member taking two `Int64`s, so two identical nested calls can sit side by side
/// as its arguments.
fn with_combine2(ns: &str, tail: &str) -> String {
    let leaf = format!("{OWN}    operation combine2(x: Leaf, y: Int64, z: Int64) -> Int64 = 2\n");
    program(ns, &leaf, RIVAL_FACT, tail)
}

/// The spans (`start..end` byte offsets) of every call of `method` in rule
/// `rule_qn`'s body, in source order. Read off the stored OCCURRENCES directly: the typer
/// reports only the FIRST error in a rule body, so no diagnostic can show a second sibling's
/// location (measured: two tie-refused calls in one body yield one refusal).
fn dot_call_spans(src: &str, rule_qn: &str, method: &str) -> Vec<(u32, u32)> {
    use anthill_core::kb::node_occurrence::{for_each_child, Expr, NodeOccurrence};
    use std::rc::Rc;
    let kb = crate::common::load_kb_with(src);
    let sym = kb
        .try_resolve_symbol(rule_qn)
        .unwrap_or_else(|| panic!("symbol {rule_qn} not found"));
    let rid = *kb
        .rules_by_functor(sym)
        .first()
        .unwrap_or_else(|| panic!("no rule for {rule_qn}"));
    let mut out = Vec::new();
    let mut stack: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).iter().rev().cloned().collect();
    while let Some(n) = stack.pop() {
        if let Some(e) = n.as_expr() {
            // The typer lowers a resolved method call to the plain application
            // (`leaf().get()` is stored as `get(leaf)`), keeping the call's node and span;
            // either spelling is the call.
            let called = match e {
                Expr::DotApply { name, .. } => Some(*name),
                Expr::Apply { functor, .. } => Some(*functor),
                _ => None,
            };
            if called.is_some_and(|f| kb.local_name_of(f) == method) {
                out.push((n.span.span.start, n.span.span.end));
            }
            let mut kids = Vec::new();
            for_each_child(e, |c| kids.push(Rc::clone(c)));
            stack.extend(kids.into_iter().rev());
        }
    }
    out.sort();
    out
}

/// THE CASE. `leaf().get()` written TWICE inside one rule-body method call is ONE hash-consed
/// term, so the materializer's table located both at the first. Built from the parse node,
/// each call is its own node with its own span.
#[test]
fn identical_sibling_calls_are_each_located_at_their_own_site() {
    let src = r#"namespace test.wi753.siblings
  import anthill.prelude.Int64

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    operation get(x: Leaf) -> Int64 = 7
    operation combine2(x: Leaf, y: Int64, z: Int64) -> Int64 = 2
  end

  rule answer(?r) :- leaf().combine2(leaf().get(), leaf().get(), ?r)
end
"#;
    let spans = dot_call_spans(src, "test.wi753.siblings.answer", "get");
    let at = |nth: usize| {
        let (line, col) = site(src, "leaf().get()", nth)
            .split_once(':')
            .map(|(l, c)| (l.parse::<usize>().unwrap(), c.parse::<usize>().unwrap()))
            .unwrap();
        let line_start: usize = src.lines().take(line - 1).map(|l| l.len() + 1).sum();
        (line_start + col - 1) as u32
    };
    assert_eq!(spans.len(), 2, "two `get` calls in the body: {spans:?}");
    assert_eq!(
        (spans[0].0, spans[1].0),
        (at(0), at(1)),
        "each identical call starts at its OWN offset, not both at the first: {spans:?}"
    );
}

/// CONTROL, passes either way: a single nested call is located at the call — the native build
/// must not lose what the per-atom table already gave (WI-1039).
#[test]
fn a_single_nested_call_is_located_at_the_call() {
    let ns = "test.wi753.single";
    let src = with_combine2(ns, "  rule answer(?r) :- leaf().combine2(leaf().describe(), 1, ?r)\n");
    let msg = refusal(&src);
    assert_eq!(
        located(&msg).0,
        site(&src, "leaf().describe()", 0),
        "the refusal must name the nested call: {msg}"
    );
}


/// Every `Expr::If` in rule `rule_qn`'s body, as `(cond, then, else)` spans.
fn if_spans(src: &str, rule_qn: &str) -> Vec<[(u32, u32); 3]> {
    use anthill_core::kb::node_occurrence::{for_each_child, Expr, NodeOccurrence};
    use std::rc::Rc;
    let kb = crate::common::load_kb_with(src);
    let sym = kb
        .try_resolve_symbol(rule_qn)
        .unwrap_or_else(|| panic!("symbol {rule_qn} not found"));
    let rid = *kb
        .rules_by_functor(sym)
        .first()
        .unwrap_or_else(|| panic!("no rule for {rule_qn}"));
    let sp = |n: &Rc<NodeOccurrence>| (n.span.span.start, n.span.span.end);
    let mut out = Vec::new();
    let mut stack: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
    while let Some(n) = stack.pop() {
        if let Some(e) = n.as_expr() {
            if let Expr::If { condition, then_branch, else_branch } = e {
                out.push([sp(condition), sp(then_branch), sp(else_branch)]);
            }
            for_each_child(e, |c| stack.push(Rc::clone(c)));
        }
    }
    out
}

/// The pattern under each import spelling: the reflect form's functor UNRESOLVED (only the
/// enum imported — how `typing_pass_spec.anthill` writes it) and RESOLVED (the members
/// imported). The two take different builders; both must locate each child at its own site.
const REFLECT_PATTERNS: [&str; 2] = [
    r#"namespace test.wi753.reflect
  import anthill.reflect.{NodeOccurrence, Expr, occurrence_term}

  rule probe(?e) :- occurrence_term(?e, if_expr(cond: ?c, then_branch: var_ref(name: a), else_branch: var_ref(name: a)))
end
"#,
    r#"namespace test.wi753.reflect
  import anthill.reflect.{NodeOccurrence, occurrence_term}
  import anthill.reflect.Expr.{if_expr, var_ref}

  rule probe(?e) :- occurrence_term(?e, if_expr(cond: ?c, then_branch: var_ref(name: a), else_branch: var_ref(name: a)))
end
"#,
];

fn offset(src: &str, needle: &str, nth: usize) -> u32 {
    src.match_indices(needle)
        .nth(nth)
        .unwrap_or_else(|| panic!("fixture guard: occurrence {nth} of {needle:?}"))
        .0 as u32
}

/// THE CASE. The two `var_ref(name: a)` branches are one hash-consed term; built from the
/// parse node, each branch is located at its own site.
#[test]
fn identical_reflect_pattern_children_are_each_located_at_their_own_site() {
    for src in REFLECT_PATTERNS {
        let ifs = if_spans(src, "test.wi753.reflect.probe");
        assert_eq!(ifs.len(), 1, "the pattern reads as one `if`: {ifs:?}\n{src}");
        let [_, then_b, else_b] = ifs[0];
        let needle = "var_ref(name: a)";
        assert_eq!(
            (then_b.0, else_b.0),
            (offset(src, needle, 0), offset(src, needle, 1)),
            "each identical branch starts at its OWN offset: {ifs:?}\n{src}"
        );
    }
}

/// CONTROL, passes either way: the written `if_expr(…)` still reads as the keyed `if`
/// occurrence — the native build keeps `visit_fn`'s reading.
#[test]
fn a_reflect_pattern_still_reads_as_its_keyed_form() {
    for src in REFLECT_PATTERNS {
        let ifs = if_spans(src, "test.wi753.reflect.probe");
        assert_eq!(ifs.len(), 1, "the pattern reads as one `if`: {ifs:?}\n{src}");
        assert_eq!(ifs[0][0].0, offset(src, "?c", 0), "cond at its site: {ifs:?}\n{src}");
    }
}

/// A RECEIVER BRACKET ON A REFLECT-NAMED CALL IS STILL REFUSED, NOT DROPPED. A user operation
/// whose name is a reflect form's (`apply`) takes the generic native build and is re-read at
/// the tail into the keyed occurrence, which has no receiver-type slot — so that build must
/// leave the bracket UNCONSUMED for `check_unconsumed_recv_types` to report, as it did when
/// the node took the round trip. MEASURED: with the generic build's `recv_type` gate removed
/// (always `build_recv_type`), this program loads CLEAN. Found by `/code-review`.
#[test]
fn a_receiver_bracket_on_a_reflect_named_call_is_refused() {
    let src = r#"namespace test.wi753.bracket
  import anthill.prelude.Int64

  sort Bx
    import anthill.prelude.Int64
    entity bx
    operation apply(x: Bx) -> Int64 = 1
  end

  rule probe(?v) :- eq(?v, Bx[T = Int64].apply(bx()))
end
"#;
    let errs = crate::common::load_errors_of(src);
    assert!(
        errs.iter().any(|e| e.contains("not read here")),
        "the bracket must be refused, not dropped: {errs:#?}"
    );
}
