//! WI-20260902-2NXAC — A COLLECTION LITERAL'S OCCURRENCE IS BUILT FROM ITS PARSE NODE.
//!
//! WI-20260902-2SZ88 took ENTITY CONSTRUCTORS off `build_body_atom_occurrence`'s
//! round-trip through `materialize_from_handle_spanned` — 126 813 of the 127 097 censused
//! nodes. It left the 284 reflect-keyed ones, because a reflect form's occurrence is not
//! an `Expr::Apply` and its shape lives in `visit_fn`. This ticket takes the three
//! COLLECTION LITERALS, which are 192 of that 284 and carry every row 2NXAC and
//! WI-20260902-4NEKZ measure: `[a, b]`, `{a, b}`, `(a, b)`.
//!
//! `Loader::collection_literal_expr` pairs each surface's lowered slots with its written
//! children — index for a list or set, label for a tuple — and runs each pair through
//! `Loader::lowered_child_occurrence`, the same three-way rule the entity arm uses. `[a, b]`
//! needs one more step: WI-1096 LOWERS it to a `cons`/`nil` spine, so the KB tree has MORE
//! NODES than the parse tree. `Loader::cons_spine_expr` walks the spine and the written
//! elements together; the cells and the terminating `nil` are the lowering's own and are
//! rebuilt, each `head` is a written element and is built from its parse node.
//!
//! ── THE STRUCTURE IS UNCHANGED, AND THAT WAS CHECKED ─────────────────────────
//!
//! A lowered list rebuilds as `Expr::Apply` under `cons` with named `head`/`tail` — what
//! `visit_fn`'s `_` arm produces — and NOT the `Expr::Constructor` that
//! `node_occurrence::build_occurrence_cons_list` builds for the bare-`nil` pattern
//! convention. Those two shapes coexist on purpose, and picking the wrong one would
//! silently change how a rule body's list matches. Verified by dumping the whole
//! occurrence tree for `[a] <=> [b]`, `{a} <=> {b}` and `(a, 1) <=> (b, 1)` before and
//! after: byte-identical except the ONE node this ticket is about, which goes from
//! `Expr::Ref(seven)` to `Expr::Apply { seven }`.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! Back it out by making the `collection_literal_expr` call site pass `None`, which sends
//! every collection literal down the round-trip again. [`a_nullary_op_in_a_collection_literal_is_a_call`]
//! goes red on **eight** of its eleven rows; its three `plus1(6)` rows are green either
//! way BY DESIGN — an APPLIED operation in the same literal already answered 1, which is
//! what says the axis is the nullary READING and not the collection.
//!
//! [`the_dot_chain_bit_needs_no_table_in_a_collection_literal`] is green under that
//! back-out too, and needs its own axis — see its doc.
//!
//! **THE RECEIVER-TYPE AXIS IS SHARED WITH WI-20260902-2SZ88.**
//! [`a_form_three_receiver_type_under_a_literal_is_not_refused`] goes red on FOUR rows
//! under that same back-out — three needing `collection_literal_expr` and one needing
//! `entity_ctor_expr` — with its bare row green either way. It is the only test in the
//! suite that reaches finding (2), which the ticket filed as PLAUSIBLE, NOT DRIVEN.
//!
//! **THE DESCRIPTION AXIS IS SEPARATE.** `Loader::descs_emitted_by_convert` ignored around
//! `collection_literal_children` — the state this ticket's first cut shipped — reddens
//! **exactly** [`an_inline_description_inside_a_literal_is_emitted_once`], on its three
//! literal rows, with its generic-atom control green. Measured.
//!
//! ── WHAT IS LEFT OF THE TICKET, AND WHY I COULD NOT DRIVE IT ─────────────────
//!
//! The other 92 reflect-keyed nodes are NOT covered here, and I could not build a fixture
//! that separates their behaviour from an unrelated one:
//!
//! * `let` does not PARSE in a rule body at all (`syntax error near z`).
//! * `if` in a rule body answers 0 for EVERY variant — bare nullary, applied operation,
//!   and a plain integer literal alike — so its 0 is some other defect and a fixture
//!   built on it would credit this ticket for a repair it did not make
//!   (a homogeneous fixture cannot judge a predicate).
//! * the control-flow forms otherwise reach a rule body only as reflection PATTERNS
//!   (`occurrence_term(?e, if_expr(cond: ?c, …))`), where a nullary-CALL reading is not
//!   the question being asked.
//!
//! So the collection literals may be the whole REACHABLE residue of finding (1), and the
//! table census below is consistent with that — but "may be" is the claim, not "is".
//! WI-20260902-2NXAC keeps findings (2) and (3) and the `[simp]`-RHS relative.

use anthill_core::kb::resolve::ResolveConfig;

/// One program per row: a nullary operation, its applied twin, and a one-field entity to
/// nest inside a literal. The namespace tail is `hold` and the rule is `cc` deliberately —
/// a namespace whose tail matches the rule name SHADOWS it and every row silently answers
/// 0, which is not the defect any row here is about.
fn answers(body: &str) -> usize {
    let src = format!(
        "namespace zz2nx.hold\n  import anthill.prelude.Int64\n  \
         import anthill.prelude.List\n  \
         operation seven() -> Int64 = 7\n  \
         operation plus1(n: Int64) -> Int64 = n + 1\n  \
         sort Bva\n    entity boxedva(x: Int64)\n  end\n  \
         rule cc(1) :- {body}\nend\n"
    );
    let mut kb = crate::common::load_kb_with(&src);
    let goal = crate::common::query_pattern_term(&mut kb, "zz2nx.hold.cc(?v)");
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// **A — THE CAPABILITY.** A nullary operation named inside a list, set or tuple literal
/// is that operation's CALL, in both spellings.
///
/// WI-20260902-CZJ2N made `:- seven` and `:- seven()` one occurrence so `reduce_op_value`
/// can open them. The round-trip bypassed that: `nullary_canon` folds `Fn{seven,[],[]}` to
/// `Term::Ref(seven)` and `visit_term`'s `Term::Ref` arm builds a plain `Expr::Ref` that
/// `reduce_op_value` hands straight back un-reduced, so the equation compared a SYMBOL
/// with a number and failed silently.
///
/// MEASURED — definite answers, baseline → with the change:
///
/// | body | before | after |
/// |---|---|---|
/// | `seven <=> 7`, `seven() <=> 7`, `plus1(6) <=> 7` | 1 | 1 |
/// | `boxedva(x: seven) <=> boxedva(x: 7)` (2SZ88's)  | 1 | 1 |
/// | `[plus1(6)] <=> [7]`                             | 1 | 1 |
/// | `{plus1(6)} <=> {7}`                             | 1 | 1 |
/// | `(plus1(6), 1) <=> (7, 1)`                       | 1 | 1 |
/// | `[seven] <=> [7]`                                | **0** | **1** |
/// | `[seven()] <=> [7]`                              | **0** | **1** |
/// | `{seven} <=> {7}`                                | **0** | **1** |
/// | `{seven()} <=> {7}`                              | **0** | **1** |
/// | `(seven, 1) <=> (7, 1)`                          | **0** | **1** |
/// | `[[seven]] <=> [[7]]`                            | **0** | **1** |
/// | `[boxedva(x: seven)] <=> [boxedva(x: 7)]`        | **0** | **1** |
/// | `[seven, plus1(6)] <=> [7, 7]`                   | **0** | **1** |
///
/// THE THREE `plus1(6)` ROWS ARE THE CONTROL AND THEY ARE ONE PER SURFACE, deliberately:
/// an APPLIED operation in the same literal already answered 1, so nesting per se was
/// never the defect. One control would have covered only one surface, and the three
/// surfaces take three different code paths here — a lowered `cons` spine, a `SetLiteral`
/// whose elements stay positional, and a `TupleLiteral` whose labels are its identity.
///
/// THE LAST THREE ROWS ARE THE RECURSION: a literal inside a literal, an ENTITY inside a
/// literal (so the two natives compose), and a literal holding a written element BESIDE a
/// bare one — which is the row that would fail if the spine walk paired elements by the
/// wrong index.
#[test]
fn a_nullary_op_in_a_collection_literal_is_a_call() {
    for (label, body) in [
        ("bare, un-nested — control", "seven <=> 7"),
        ("parens, un-nested — control", "seven() <=> 7"),
        ("an APPLIED op in a LIST — the control for the spine", "[plus1(6)] <=> [7]"),
        ("an APPLIED op in a SET — the control for that surface", "{plus1(6)} <=> {7}"),
        ("an APPLIED op in a TUPLE — the control for that surface", "(plus1(6), 1) <=> (7, 1)"),
        ("a bare nullary op in a LIST literal", "[seven] <=> [7]"),
        ("…and its parenthesised spelling", "[seven()] <=> [7]"),
        ("a bare nullary op in a SET literal", "{seven} <=> {7}"),
        ("…and its parenthesised spelling", "{seven()} <=> {7}"),
        ("a bare nullary op in a TUPLE", "(seven, 1) <=> (7, 1)"),
        ("a literal INSIDE a literal", "[[seven]] <=> [[7]]"),
        ("an ENTITY inside a literal — the two natives compose", "[boxedva(x: seven)] <=> [boxedva(x: 7)]"),
        ("a bare one BESIDE a written one — pairing by index", "[seven, plus1(6)] <=> [7, 7]"),
    ] {
        assert_eq!(
            answers(body),
            1,
            "{label}: `{body}` must answer 1. A 0 is the collection-literal round-trip \
             handing the atom to a TERM walk, where a nullary op is a bare `Term::Ref` \
             that `reduce_op_value` cannot open — so the equation compares the SYMBOL \
             `seven` with 7 and fails silently."
        );
    }
}

/// The fixture `wi_4nekz_dotted_equation_operand_test` uses, kept identical to it on
/// purpose: `zz4n.inner.rel` is a real one-clause relation and `body` sits in a rule body
/// one namespace over.
fn rule_body_with(extra: &str, body: &str) -> Vec<String> {
    let src = format!(
        "namespace zz4n.inner\n  fact base4n(1)\n  rule rel(1) :- base4n(1)\nend\n\
         namespace zz4n.two\n  fact base4n2(1)\n  rule rel2(1) :- base4n2(1)\n{extra}  \
         rule r(1) :- {body}\nend\n"
    );
    crate::common::try_load_kb_with(&src).err().unwrap_or_default()
}

/// **B — AND THE DOT-CHAIN BIT NO LONGER COMES FROM A TABLE.**
///
/// `Loader::parse_dot_chain_table` keys on the HASH-CONSED KB `TermId`, which is
/// many-to-one, and pays for that with a set difference that withholds the bit wherever a
/// citation shares a term with a written `field_access` call. With the collection
/// literals built from their parse nodes, their children take the bit from
/// `dotted_citation_name` of their own node instead.
///
/// DRIVEN BY EMPTYING THE TABLE, which is the only way to tell "the bit is right" from
/// "the bit is right because the table happened to have it". With `parse_dot_chain_table`
/// returning an EMPTY set, MEASURED per row across all three trees:
///
/// | rule body | before 2SZ88 | after 2SZ88 | after this |
/// |---|---|---|---|
/// | `zz4n.inner.rel = 7` — control, never took the return | 1, typed | 1, typed | 1, typed |
/// | `boxed4n(v: zz4n.inner.rel) = 7`  | 3, none | **1, typed** | 1, typed |
/// | `[zz4n.inner.rel] = 7`            | 3, none | 3, none | **1, typed** |
/// | `{zz4n.inner.rel} = 7`            | 3, none | 3, none | **1, typed** |
/// | `(zz4n.inner.rel, 1) = 7`         | 3, none | 3, none | **1, typed** |
///
/// AND THE TABLE'S OWN STATE, IN THREE PARTS — because "is it still reachable" is not
/// one question, and an earlier version of this note answered it as if it were:
///
/// * STILL CALLED: 108 times over `wi_tests`, mostly `dot_apply` (76).
/// * ALWAYS EMPTY: 0 of those 108 returned anything. Not structurally dead, though — a
///   hand-written `?b.take(zz4n.inner.rel)` (a citation as a `dot_apply` ARGUMENT) makes
///   it `cited = 2`.
/// * AND ITS RESULT CHANGES NOTHING REACHABLE: emptying it leaves the whole `wi_tests`
///   binary green, and gives byte-identical diagnostics even on that `cited = 2` program.
///
/// It is kept on an ASYMMETRY rather than on evidence of use — a lost diagnostic is
/// recoverable, a written `field_access` laundered into a name it does not spell is
/// WI-20260901-92VA4's silent acceptance and is not. `Loader::parse_dot_chain_table`'s
/// doc carries the numbers, and what a future reader should re-run before deleting it.
///
/// THIS TEST RUNS WITH THE TABLE INTACT and asserts the ordinary behaviour, so it is
/// GREEN under a plain back-out of the native arm — the table supplies the bit there. The
/// figures above are the two-axis measurement, run by hand, and recorded here because a
/// test cannot assert them without shipping the probe.
#[test]
fn the_dot_chain_bit_needs_no_table_in_a_collection_literal() {
    const BOXED: &str = "  sort Boxed2n\n    entity boxed2n(v: Int64)\n  end\n";
    for (label, body, wants) in [
        ("bare — the control, green under every variant", "zz4n.inner.rel = 7", "eq.b (op-arg)"),
        ("in a list literal", "[zz4n.inner.rel] = 7", "List[T = Relation"),
        ("in a set literal", "{zz4n.inner.rel} = 7", "Set[T = Relation"),
        ("in a tuple", "(zz4n.inner.rel, 1) = 7", "_1: Relation"),
        ("in an entity constructor argument — 2SZ88's row", "boxed2n(v: zz4n.inner.rel) = 7", "boxed2n.v (entity-field)"),
    ] {
        let errs = rule_body_with(BOXED, body);
        assert_eq!(
            errs.len(),
            1,
            "{label}: `{body}` writes ONE name and must get ONE diagnosis. THREE is the \
             per-segment cascade over a name that RESOLVES; ZERO is the opposite defect, \
             the chain silently accepted. Got {}: {errs:#?}",
            errs.len()
        );
        assert!(
            !errs[0].contains("unresolved"),
            "{label}: …and a name that resolves must not be called unresolved: {:?}",
            errs[0]
        );
        assert!(
            errs[0].contains("Relation["),
            "{label}: …and the chain must have been TYPED as the relation it cites: {:?}",
            errs[0]
        );
        assert!(
            errs[0].contains(wants),
            "{label}: …inside the enclosing atom it was written in (expected {wants:?}): {:?}",
            errs[0]
        );
    }
}

/// **C — AND AN INLINE DESCRIPTION INSIDE A LITERAL IS EMITTED ONCE.**
///
/// `collection_literal_expr` calls `convert_term` on the subtree — that walk emits a
/// `DescriptionInfo` for every described variable in it — and then recurses into the same
/// elements, whose `Term::Var(Var::Global(..))` arm emits them AGAIN. `emit_desc_fact`
/// indexes per target, so the second walk makes a DISTINCT fact rather than colliding.
///
/// THIS IS THE SECOND TIME THE SAME ROOT CAUSE SHIPPED. WI-20260902-2SZ88 hit it for
/// entity constructors and fixed it with `Loader::descs_emitted_by_convert`; this
/// ticket's first cut added a second two-walk function and did not set the flag. Both
/// save/restores now wrap a SPLIT-OUT function rather than a loop body, so a later
/// `return` inside cannot skip the restore. Found by `/code-review` both times.
///
/// MEASURED, `DescriptionInfo` facts by content, with the change → with
/// `collection_literal_expr` returning `None`:
///
/// | rule body | first cut | fixed | back-out |
/// |---|---|---|---|
/// | `some_pred([?x {< … >}?])`     | **2** | 1 | 1 |
/// | `some_pred({?x {< … >}?})`     | **2** | 1 | 1 |
/// | `some_pred((?x {< … >}?, 1))`  | **2** | 1 | 1 |
/// | `some_pred(?x {< … >}?)` — control | 1 | 1 | 1 |
///
/// THE CONTROL IS THE GENERIC ATOM: 1 under every variant, which is what says the
/// duplicate belongs to the collection walk and not to the emitter.
#[test]
fn an_inline_description_inside_a_literal_is_emitted_once() {
    use anthill_core::kb::term::{Literal, Term};
    for (label, body, needle) in [
        ("in a LIST literal", "some_pred([?x {< the list value >}?])", "the list value"),
        ("in a SET literal", "some_pred({?x {< the set value >}?})", "the set value"),
        ("in a TUPLE", "some_pred((?x {< the tuple value >}?, 1))", "the tuple value"),
        (
            "in a GENERIC atom — the control, 1 under every variant",
            "some_pred(?x {< the plain value >}?)",
            "the plain value",
        ),
    ] {
        let source = format!("namespace zz2nx.d\n  rule r(?x)\n    :- {body}\nend\n");
        let mut kb = anthill_core::kb::KnowledgeBase::new();
        let parsed = anthill_core::parse::parse(&source).expect("parse failed");
        // Stops before the typer: the subject is what the LOADER records, over a fixture
        // (`some_pred` is undeclared) deliberately incomplete for the passes above it.
        anthill_core::kb::load::load_all_with(
            &mut kb,
            &[&parsed],
            &anthill_core::kb::load::NullResolver,
            anthill_core::kb::load::LoadOptions {
                run_typer: false,
                ..Default::default()
            },
        )
        .expect("load failed");
        let desc_sym = kb
            .try_resolve_symbol("anthill.reflect.DescriptionInfo")
            .expect("the reflect sort is registered by the prelude");
        let n = kb
            .rules_by_functor(desc_sym)
            .iter()
            .filter(|&&rid| match kb.get_term(kb.rule_head(rid)) {
                Term::Fn { named_args, .. } => named_args
                    .iter()
                    .find(|(f, _)| kb.local_name_of(*f) == "content")
                    .map(|(_, v)| *v)
                    .is_some_and(|v| {
                        matches!(kb.get_term(v), Term::Const(Literal::String(s)) if s == needle)
                    }),
                _ => false,
            })
            .count();
        assert_eq!(
            n, 1,
            "{label}: one written description is ONE fact. `emit_desc_fact` indexes per \
             target, so a second walk over the same subtree makes a distinct fact rather \
             than colliding — got {n}."
        );
    }
}

/// **D — AND A FORM-(3) RECEIVER TYPE UNDER A LITERAL IS NO LONGER FALSELY REFUSED.**
///
/// WI-20260902-2NXAC's finding (2), which the ticket filed as PLAUSIBLE, NOT DRIVEN. It is
/// driven now, and it was already repaired by the two native arms — this row is what says
/// so, because nothing else in the suite reaches it.
///
/// THE MECHANISM. Proposal 035 form (3) writes a companion receiver's type on an operation
/// call: `Map[K = String, V = Int64].empty()`. `Loader::build_recv_type` reads that bracket
/// AND marks the parse node consumed; `Loader::check_unconsumed_recv_types` then sweeps
/// every parse node still carrying an unread one and refuses it. The round-trip called
/// NEITHER — `materialize_from_handle_spanned` walks the KB term, and `build_recv_type`
/// has no call site reachable from inside a materialized subtree — so a form-(3) call
/// nested in a literal or an entity argument was written, never consumed, and then refused
/// by the sweep, asserting the callee "is not a call whose result it can type" about a
/// callee that IS an operation call.
///
/// Both native arms fixed it without aiming at it: every child goes through
/// `build_body_atom_occurrence`, whose generic-application arm reads `build_recv_type`.
///
/// MEASURED — `load` errors mentioning "not read here", baseline → with both arms:
///
/// | rule body | before | after |
/// |---|---|---|
/// | `?v <=> Map[…].empty()` — the control, never took the return | 0 | 0 |
/// | `?v <=> [Map[…].empty()]` — the ticket's own example         | **1** | 0 |
/// | `?v <=> {Map[…].empty()}`                                    | **1** | 0 |
/// | `?v <=> (Map[…].empty(), 1)`                                 | **1** | 0 |
/// | `?v <=> boxm(m: Map[…].empty())` — the ENTITY arm, 2SZ88's   | **1** | 0 |
///
/// THE BARE ROW IS THE CONTROL and it is green either way: it never took the early return,
/// so a run in which only it passes measures nothing. FOUR ROWS FAIL when either native
/// arm is backed out — the entity row needs `entity_ctor_expr`, the other three need
/// `collection_literal_expr`, so this one test covers both tickets' halves of finding (2).
///
/// STILL NOT COVERED, and stated because the row would look total otherwise: a form-(3)
/// receiver on a ZERO-FIELD constructor. `entity_ctor_expr`'s `Term::Ref` arm (the
/// `nullary_canon` fold) returns before the `Expr::Apply` tail and an `Expr::Ref` has no
/// `recv_type` slot to put one in, so that shape is still unconsumed. I could not build a
/// program for it; the hole is recorded at that arm.
#[test]
fn a_form_three_receiver_type_under_a_literal_is_not_refused() {
    for (label, body) in [
        (
            "bare in a rule body — the control, green either way",
            "?v <=> Map[K = String, V = Int64].empty()",
        ),
        (
            "inside a LIST literal — the ticket's own example",
            "?v <=> [Map[K = String, V = Int64].empty()]",
        ),
        ("inside a SET literal", "?v <=> {Map[K = String, V = Int64].empty()}"),
        ("inside a TUPLE", "?v <=> (Map[K = String, V = Int64].empty(), 1)"),
        (
            "inside an ENTITY constructor argument — WI-20260902-2SZ88's half",
            "?v <=> boxm(m: Map[K = String, V = Int64].empty())",
        ),
    ] {
        let src = format!(
            "namespace zz2nx.f3\n  import anthill.prelude.Int64\n  \
             import anthill.prelude.String\n  import anthill.prelude.List\n  \
             import anthill.prelude.Map\n  \
             sort Bm\n    entity boxm(m: Map[K = String, V = Int64])\n  end\n  \
             rule cc(1) :- {body}\nend\n"
        );
        let errs = crate::common::try_load_kb_with(&src).err().unwrap_or_default();
        let unread: Vec<&String> = errs.iter().filter(|e| e.contains("not read here")).collect();
        assert!(
            unread.is_empty(),
            "{label}: `{body}` writes a form-(3) receiver on an OPERATION call, so the \
             bracket must be READ, not swept up as unconsumed. The sweep's message asserts \
             the callee `is not a call whose result it can type` — about a callee that is \
             exactly that: {unread:#?}"
        );
        assert!(
            errs.is_empty(),
            "{label}: …and the program must load clean: {errs:#?}"
        );
    }
}
