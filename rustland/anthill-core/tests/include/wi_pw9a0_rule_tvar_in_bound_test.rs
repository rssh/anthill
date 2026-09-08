//! WI-20260908-PW9A0 — a rule head's `[A]` TYPE-VARIABLE INTRODUCER may be written
//! anywhere inside a bound, not only as the whole bound.
//!
//! WI-582 gave `rule g[A](?a: A, …) :- …, Summable[A]` its meaning by substitution: `A`
//! denotes the sort its body guard bounds it with, so the annotation means
//! `conforms(typeof(?a), Summable)` (`docs/kernel-language.md` §5.3). It implemented
//! that only for a bound that IS the bare variable — a one-segment `TypeExpr::Simple`
//! special case ahead of the ordinary lowering — so one level in
//! (`?a: List[T = A]`) the name fell through to ordinary resolution and the load
//! reported `unresolved name 'A'` about a variable the same head introduced three tokens
//! earlier, advising the author to declare or import it. The substitution now happens at
//! the RESOLUTION (`Loader::rule_head_bound_alias`), which is why it holds at every depth
//! and in both spellings without either one naming a `TypeExpr` shape.
//!
//! WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT — FOUR SEPARABLE AXES, each MEASURED
//! by mutating its own site and re-running this file (the counts below are that run's):
//!
//!  * **The substitution's RELOCATION** — `rule_head_bound_alias` returning `None` at the
//!    three resolution funnels, with the `TypeExpr::Simple` special case restored: the
//!    pre-ticket code. **8 of 11 fail** — everything except
//!    [`the_control_a_bare_introducer_drives`],
//!    [`a_concrete_bound_with_no_nominal_head_suspends`] and
//!    [`the_sigil_free_bare_spelling_was_a_dead_clause`] (that last one is on the FILTER
//!    axis, not this one, which is what tells the two apart). `wi582` and `wi619` stay
//!    green under it — that is what makes it a back-out of the RELOCATION and not of
//!    WI-582 itself.
//!  * **`convert_rule_head_with_params`' ParseAux FILTER** (restore the blanket decline).
//!    **3 fail**, and only one is about a compound bound:
//!    [`the_sigil_free_spelling_answers_identically`],
//!    [`the_sigil_free_bare_spelling_was_a_dead_clause`] — which goes back to answering 0
//!    from a CLEAN load, the row that shows why the decline had to go — and
//!    [`an_unbounded_introducer_reports_one_fault_not_two`] (its sigil-free row reports
//!    twice again). It is also the only axis `wi742`'s own
//!    `a_head_carrying_a_type_var_introducer_is_reclassified_like_any_other` fails on.
//!  * **Seeding `rule_tvar_bounds` with the UNBOUNDED introducers.** **Exactly 1 fails**:
//!    [`an_unbounded_introducer_reports_one_fault_not_two`] (2 load errors, not 1).
//!  * **The SHADOWING refusal** in `load_rule`. **Exactly 1 fails**:
//!    [`an_introducer_may_not_shadow_a_name_in_scope`]. Its own axis, and separate from
//!    the relocation on purpose — the relocation is what makes the shadowing reach depth,
//!    the refusal is what stops that being a silent change of meaning.
//!  * **`typing::type_bound_verdict`'s predicate** (variable → nominal, the pre-ticket
//!    form). **3 fail**, and none of them mentions an introducer in its own right:
//!    [`a_concrete_bound_with_no_nominal_head_restricts`],
//!    [`and_it_holds_where_the_value_does_conform`] and
//!    [`so_does_one_with_an_introducer_substituted_into_it`] — the last is where this
//!    axis and the RELOCATION meet, which is why the first two carry no introducer at all.
//!
//! [`the_control_a_bare_introducer_drives`] passes under ALL FIVE back-outs BY DESIGN —
//! it writes no introducer inside a bound and its bound is nominal. It is the yardstick
//! the rows above are read against, not a duplicate of them.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// A two-row table whose rows are TAGGED by their second column, so which row a bound
/// keeps is asserted by VALUE (`g(?a, 7)` vs `g(?a, 8)`) and not by a count that any
/// one-row outcome would satisfy. Two tables, because the two questions need different
/// carriers and sharing one would make a row measure the wrong thing:
///
///  * `list_src` holds `[1, 2]` (a `List[T = Int64]`, whose ELEMENT type provides
///    `Summable`) and `[true]` (a `List[T = Bool]`, whose element type does not). This
///    is the table a COMPOUND bound `List[T = A]` discriminates. A BARE `Summable` bound
///    refutes BOTH of its rows — a `List` carrier does not itself provide `Summable` —
///    which is exactly why an author reaches for the compound form, and which
///    [`a_compound_bound_filters_by_the_introducers_bound`] ASSERTS rather than assumes.
///  * `scalar_src` holds `1` and `true` directly, which is the table a BARE bound
///    discriminates. The bare-bound rows use it so their yardstick is a bound that
///    actually decides.
fn list_src(ns: &str, rule: &str) -> String {
    table_src(ns, "[1, 2]", "[true]", rule)
}

/// The scalar peer of [`list_src`] — same shape, same tags, carriers a BARE bound can
/// decide.
fn scalar_src(ns: &str, rule: &str) -> String {
    table_src(ns, "1", "true", rule)
}

fn table_src(ns: &str, conforming: &str, other: &str, rule: &str) -> String {
    format!(
        r#"
namespace test.pw9a0.{ns}
  import anthill.prelude.{{Int64, Bool, Eq, List}}

  sort Summable
    sort T = ?
    requires Eq[T]
  end

  fact Summable[T = Int64]

  fact src({conforming}, 7)
  fact src({other}, 8)

  {rule}

  -- THE FACT-LEVEL CONTROL: the same table, the same two columns, no annotation. It is
  -- what makes a one-row answer above a FILTER rather than a table that only ever had
  -- one row.
  rule ungated(?a, ?b) :- src(?a, ?b)
end
"#
    )
}

/// `rule g[A](?a: A, …) :- …, Summable[A]` — WI-582's own shape, which has worked all
/// along. IT PASSES WITH THIS TICKET'S CHANGE BACKED OUT, BY DESIGN: it is the yardstick
/// the compound rows are measured against (same guard, same table, same answers), and
/// the ticket names it the control that makes the failure a report rather than a guess.
#[test]
fn the_control_a_bare_introducer_drives() {
    let mut kb = crate::common::load_kb_with(&scalar_src(
        "control",
        "rule g[A](?a: A, ?b: Int64) :- src(?a, ?b), Summable[A]",
    ));
    assert_eq!(answers(&mut kb, "test.pw9a0.control.ungated(?a, ?b)"), 2);
    // `?a: A` ≡ `?a: Summable`: `1` carries `Int64`, which provides it; `true` carries
    // `Bool`, which does not.
    assert_eq!(answers(&mut kb, "test.pw9a0.control.g(?a, 7)"), 1);
    assert_eq!(answers(&mut kb, "test.pw9a0.control.g(?a, 8)"), 0);
}

/// THE TICKET'S FAILING ROW, sigil spelling. `?a: List[T = A]` is "a list whose element
/// type is the bounded A", and it is DRIVEN: the clause answers, and the row whose
/// element type does not provide `Summable` is filtered.
#[test]
fn a_compound_bound_filters_by_the_introducers_bound() {
    let mut kb = crate::common::load_kb_with(&list_src(
        "sigil",
        "rule g[A](?a: List[T = A], ?b: Int64) :- src(?a, ?b), Summable[A]\n  \
         rule bare[A](?a: A, ?b: Int64) :- src(?a, ?b), Summable[A]",
    ));
    assert_eq!(answers(&mut kb, "test.pw9a0.sigil.ungated(?a, ?b)"), 2);
    // THE BOUND'S OWN CONTRAST, on the same two rows: the BARE spelling of the same
    // introducer keeps NEITHER, a `List` carrier not itself providing `Summable`. So the
    // rows below are the compound bound answering a question the bare one cannot ask,
    // not a second way of writing it.
    assert_eq!(answers(&mut kb, "test.pw9a0.sigil.bare(?a, ?b)"), 0);
    assert_eq!(
        answers(&mut kb, "test.pw9a0.sigil.g(?a, 7)"),
        1,
        "the `[1, 2]` row's element type Int64 provides Summable — it must be KEPT"
    );
    assert_eq!(
        answers(&mut kb, "test.pw9a0.sigil.g(?a, 8)"),
        0,
        "the `[true]` row's element type Bool does not provide Summable — it must be \
         FILTERED; this is the assertion a clean load cannot make"
    );
}

/// BOTH SPELLINGS, ONE ANSWER (proposal 060 §2.1). The same program with the sigil
/// dropped must give the same numbers — the parameter form lowers to the same internal
/// binding, so a divergence here is a divergence in the language.
#[test]
fn the_sigil_free_spelling_answers_identically() {
    let mut kb = crate::common::load_kb_with(&list_src(
        "param",
        "rule g[A](a: List[T = A], b: Int64) :- src(a, b), Summable[A]",
    ));
    assert_eq!(answers(&mut kb, "test.pw9a0.param.ungated(?a, ?b)"), 2);
    assert_eq!(answers(&mut kb, "test.pw9a0.param.g(?a, 7)"), 1);
    assert_eq!(answers(&mut kb, "test.pw9a0.param.g(?a, 8)"), 0);
}

/// THE SILENT HALF, and the reason the §2.1 reclassifier's ParseAux DECLINE could not
/// stay. `rule g[A](a: A, …)` is the sigil-free spelling of the control above. Declined,
/// its head went to the ordinary path, which left `a: A` a NAMED ARGUMENT and the body's
/// `a` an unresolved constant: MEASURED, it LOADED CLEAN and answered 0 where its sigil
/// twin answered 1 — a dead clause, with no diagnostic anywhere.
#[test]
fn the_sigil_free_bare_spelling_was_a_dead_clause() {
    let mut kb = crate::common::load_kb_with(&scalar_src(
        "parambare",
        "rule g[A](a: A, b: Int64) :- src(a, b), Summable[A]",
    ));
    assert_eq!(
        answers(&mut kb, "test.pw9a0.parambare.g(?a, ?b)"),
        1,
        "the sigil-free bare spelling must answer what its `?a: A` twin answers"
    );
    assert_eq!(answers(&mut kb, "test.pw9a0.parambare.g(?a, 7)"), 1);
    assert_eq!(answers(&mut kb, "test.pw9a0.parambare.g(?a, 8)"), 0);
}

/// NO `TypeExpr` SHAPE IS SINGLED OUT, because the substitution is a fact about
/// RESOLUTION rather than a walk over shapes. Three placements a shape-walking
/// implementation would each have had to admit separately.
#[test]
fn an_introducer_denotes_its_bound_at_any_depth() {
    // (a) NESTED one level further: `List[T = List[T = A]]`. It loads and REFUTES both
    // rows — the table holds lists of scalars, not lists of lists — which is the right
    // answer and, unlike a load-only assertion, one that a dropped inner binding
    // (silently widening the bound to `List`) would fail.
    let mut kb = crate::common::load_kb_with(&list_src(
        "nested",
        "rule g[A](?a: List[T = List[T = A]], ?b: Int64) :- src(?a, ?b), Summable[A]",
    ));
    assert_eq!(answers(&mut kb, "test.pw9a0.nested.ungated(?a, ?b)"), 2);
    assert_eq!(answers(&mut kb, "test.pw9a0.nested.g(?a, ?b)"), 0);

    // (b) TWO introducers, each with its own guard, in two different positions.
    let mut kb = crate::common::load_kb_with(&list_src(
        "two",
        "rule g[A, B](?a: List[T = A], ?b: B) :- src(?a, ?b), Summable[A], Summable[B]",
    ));
    assert_eq!(answers(&mut kb, "test.pw9a0.two.g(?a, 7)"), 1);
    assert_eq!(answers(&mut kb, "test.pw9a0.two.g(?a, 8)"), 0);

    // (c) The introducer as an APPLICATION's head — `A[T = Int64]` means
    // `Summable[T = Int64]`, which is a bound with a nominal head and so decides. A
    // shape-walking implementation would have had to choose between admitting this and
    // refusing it as higher-kinded; the substitution reading answers without a choice.
    // On the SCALAR table, so this row shows the bound HOLDING as well as refuting: over
    // the list table it refutes both, which cannot tell a working bound from one that
    // refuses everything.
    let mut kb = crate::common::load_kb_with(&scalar_src(
        "applied",
        "rule g[A](?a: A[T = Int64], ?b: Int64) :- src(?a, ?b), Summable[A]",
    ));
    assert_eq!(answers(&mut kb, "test.pw9a0.applied.ungated(?a, ?b)"), 2);
    assert_eq!(answers(&mut kb, "test.pw9a0.applied.g(?a, 7)"), 1);
    assert_eq!(answers(&mut kb, "test.pw9a0.applied.g(?a, 8)"), 0);
}

/// WI-582's ORIGINAL READER. A `[simp]` equation's typed pattern is enforced by the
/// resolver's rewrite path (`typing::typed_pattern_bounds_hold`), not by a generated
/// body goal, and it reads the SAME `type_bound_verdict` — so a compound bound has to
/// work there too, and by value: the rule fires over the conforming carrier and is left
/// intact over the other.
#[test]
fn a_simp_equation_may_carry_a_compound_bound() {
    use anthill_core::intern::Symbol;
    use anthill_core::kb::term::{Literal, Term, TermId};
    use smallvec::SmallVec;

    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.pw9a0.simp
  import anthill.prelude.{Int64, Bool, Eq, List}

  sort Summable
    sort T = ?
    requires Eq[T]
  end

  fact Summable[T = Int64]

  sort Lib
    sort E = ?
    operation {
      keep(x: List[T = E], y: Int64) -> Int64
    }
    rule {
      keep_id: keep[A](?x: List[T = A], ?y) <=> ?y :- Summable[A] [simp]
    }
  end
end
"#,
    );
    let keep = kb
        .try_resolve_symbol("test.pw9a0.simp.Lib.keep")
        .expect("keep symbol");
    let seven = kb.alloc(Term::Const(Literal::Int(7)));
    fn call(kb: &mut KnowledgeBase, keep: Symbol, seven: TermId, elems: &[Literal]) -> TermId {
        let items: Vec<_> = elems
            .iter()
            .map(|l| kb.alloc(Term::Const(l.clone())))
            .collect();
        let list = kb.build_list(&items);
        let term = kb.alloc(Term::Fn {
            functor: keep,
            pos_args: SmallVec::from_slice(&[list, seven]),
            named_args: SmallVec::new(),
        });
        kb.simplify(term)
    }
    // `[1, 2]` is a `List[T = Int64]`; Int64 provides Summable → the bound holds → fire.
    let fired = call(&mut kb, keep, seven, &[Literal::Int(1), Literal::Int(2)]);
    assert_eq!(
        kb.get_term(fired),
        &Term::Const(Literal::Int(7)),
        "keep must fire over a List[T = Int64]; got {:?}",
        kb.get_term(fired)
    );
    // `[true]` is a `List[T = Bool]` → the bound is refuted → the redex is left intact.
    let left = call(&mut kb, keep, seven, &[Literal::Bool(true)]);
    assert!(
        !matches!(kb.get_term(left), Term::Const(Literal::Int(7))),
        "keep must NOT fire over a List[T = Bool]; got {:?}",
        kb.get_term(left)
    );
}

/// AN INTRODUCER MAY NOT SHADOW A NAME IN SCOPE, and this is the row that makes the
/// substitution unambiguous rather than merely uniform.
///
/// The variable denotes its bound at EVERY depth now, so if its name also resolves the
/// same annotation has two readings. MEASURED on one program under the two codes, over
/// the list table: `rule g[Bool](?a: List[T = Bool], …) :- …, Summable[Bool]` kept the
/// `[true]` row before this ticket (`Bool` read as the SORT — byte-identical to the
/// no-introducer control) and the `[1, 2]` row after (read as the VARIABLE), LOADING
/// CLEAN both times. A silent change of meaning is not a repair, so the collision is
/// refused and the author renames the variable.
///
/// THE THREE CONTROLS are what make this a collision rule and not a blanket one: the
/// same bound with a non-colliding introducer loads, the same annotation with no
/// introducer loads and means the sort, and the WHOLE-BOUND colliding spelling is
/// refused too — the last one deliberately, because it is the position that shadowed
/// ALREADY (measured identically before and after), and leaving it admitted would keep
/// exactly the two-readings-at-two-depths split this ticket closed.
///
/// Backing the refusal out fails this row and nothing else in the file.
#[test]
fn an_introducer_may_not_shadow_a_name_in_scope() {
    for (ns, rule) in [
        (
            "shadow_depth",
            "rule g[Bool](?a: List[T = Bool], ?b: Int64) :- src(?a, ?b), Summable[Bool]",
        ),
        (
            "shadow_whole",
            "rule g[Bool](?a: Bool, ?b: Int64) :- src(?a, ?b), Summable[Bool]",
        ),
    ] {
        crate::common::expect_load_errors(
            crate::common::try_load_kb_with(&list_src(ns, rule)),
            &["rule type-variable `Bool` also names something in scope"],
        );
    }
    // CONTROL 1 — the same bound, a name that resolves to nothing. Loads, and filters.
    let mut kb = crate::common::load_kb_with(&list_src(
        "noshadow",
        "rule g[A](?a: List[T = A], ?b: Int64) :- src(?a, ?b), Summable[A]",
    ));
    assert_eq!(answers(&mut kb, "test.pw9a0.noshadow.g(?a, 7)"), 1);
    // CONTROL 2 — the same annotation with NO introducer, which is the reading the
    // refused program could otherwise have meant: it keeps the OTHER row, which is what
    // makes the two readings distinguishable and the refusal necessary.
    let mut kb = crate::common::load_kb_with(&list_src(
        "literal",
        "rule g(?a: List[T = Bool], ?b: Int64) :- src(?a, ?b)",
    ));
    assert_eq!(answers(&mut kb, "test.pw9a0.literal.g(?a, 7)"), 0);
    assert_eq!(answers(&mut kb, "test.pw9a0.literal.g(?a, 8)"), 1);
}

/// A CONSEQUENCE OF ASKING AT THE RESOLUTION, recorded because it is a real behaviour
/// change on a shape nothing in the corpus writes, and because the direction matters.
///
/// The alias hands the ordinary lowering a SYMBOL, so that lowering CLASSIFIES it —
/// where the deleted special case handed back a finished sort-ref term and classified
/// nothing. The two differ for exactly one guard: one whose FUNCTOR is itself a type
/// parameter of the enclosing sort (`:- F[T]` where `sort F = ?`). MEASURED on the two
/// codes: before, the bound was `Ref(F)`, a sort reference to a parameter symbol —
/// nominal-looking, so `type_bound_verdict` REFUTES it and the guard silently drops
/// every row; now it is that parameter's own logic `Var`, which has no nominal head, so
/// the verdict SUSPENDS and a relational clause leaves its rows CONDITIONAL instead.
///
/// Both mean the rule never fires — the rewrite reader collapses refute and suspend to
/// "don't fire", so a `[simp]` rule like this one is unaffected either way — but a
/// variable is what `F` actually is, and a loud residual is the better half of the pair
/// (`docs/kernel-language.md` §5.3, and the project's loud-over-silent rule).
#[test]
fn a_guard_whose_functor_is_a_type_parameter_lowers_as_that_parameter() {
    use anthill_core::kb::term::{Term, Var};

    let kb = crate::common::load_kb_with(
        r#"
namespace test.pw9a0.tp
  import anthill.prelude.{Int64}
  sort Lib
    sort F = ?
    operation { keep(x: F, y: Int64) -> Int64 }
    rule {
      keep_id: keep[T](?x: T, ?y) <=> ?y :- F[T] [simp]
    }
  end
end
"#,
    );
    let rid = kb
        .rule_id_by_qn("test.pw9a0.tp.Lib.keep_id")
        .expect("keep_id loaded");
    let bounds = kb.rule_type_bounds(rid);
    assert_eq!(bounds.len(), 1, "one folded bound; got {bounds:?}");
    assert!(
        matches!(kb.get_term(bounds[0].1), Term::Var(Var::Global(_))),
        "the bound must be the type PARAMETER's own variable, not a sort ref to its \
         symbol (which is what the pre-ticket special case produced); got {:?}",
        kb.get_term(bounds[0].1)
    );
}

/// AN UNTAGGED GUARDED EQUATION KEEPS ITS REFUSAL. This row exists because THIS ticket
/// (PW9A0) tried to lift the refusal for BOTH spellings and was wrong about the reason;
/// WI-20260820-8RJK8 then lifted the TAGGED half for a different reason, and the untagged
/// half is what is left.
///
/// PW9A0'S ARGUMENT, and why it did not hold: a guarded equation can never be a
/// directional rewrite (an equation is BODYLESS, §8.3), the refusal's stated reason is
/// "neither reader exists", and WI-742's `install_typed_head_domain_goals` skips only
/// `is_directional_equation` — so a guarded equation DOES get a generated `domain(?x, T)`
/// goal prepended. The bound installs and the body carries the extra goal; both are
/// observable. THE GOAL WAS NOT A READER, because nothing evaluated a matched equation's
/// body. MEASURED then, with an UNSATISFIABLE bound, three rows over one program whose
/// parameters are `Int64`:
///
/// | annotation on `pk: pick(?x: …, ?y) = ?y :- src(?x, ?y)` | `simplify(pick(1, 5))` |
/// |---|---|
/// | none | the redex, unchanged |
/// | `?x: Int64` (satisfiable) | byte-identical |
/// | `?x: Bool` (UNSATISFIABLE) | byte-identical |
///
/// WHAT 8RJK8 CHANGED, and what it did not. A guarded equation's body is now proved
/// post-match, so a `[simp]`-TAGGED one is a directional rewrite and
/// `typed_pattern_bounds_hold` enforces its bound — that half is now KEPT, and
/// `wi903_typed_bound_dot_rule_test::typed_bound_on_a_guarded_equation_follows_the_tag`
/// owns the pair. The UNTAGGED half is untouched: `[simp]` is the enablement (WI-881),
/// so nothing fires an untagged equation, guarded or not, and its bound would still be
/// decoration. The measurement above stands as the record of what "the mechanism ran"
/// is worth without a firing site behind it.
#[test]
fn an_untagged_guarded_equation_keeps_its_refusal() {
    const PROG: &str = r#"
namespace test.pw9a0.guarded
  import anthill.prelude.{Int64}
  sort Colour
    entity red
  end
  fact item(red())
  sort Lib
    sort A = ?
    operation g(x: A) -> A
    rule { law: g(?x: Colour) = ?x :- item(?x) }
  end
end
"#;
    crate::common::expect_load_errors(crate::common::try_load_kb_with(PROG), &["WI-582"]);
}

/// THE DIAGNOSTIC HALF. An introducer with no `:- Spec[A]` guard is ONE fault, and it
/// already had an accurate message naming the variable and the repair. Written inside a
/// bound it also drew `unresolved name 'A'` — the same misdirection this ticket is
/// about, whose repair (declare or import `A`) is wrong for a name the head introduced.
///
/// All three spellings, because the fault reaches the three resolution funnels by three
/// different routes and a fix at one of them would leave the others reporting twice.
#[test]
fn an_unbounded_introducer_reports_one_fault_not_two() {
    for (ns, rule) in [
        ("ub_bare", "rule g[A](?a: A, ?b: Int64) :- src(?a, ?b)"),
        (
            "ub_param",
            "rule g[A](?a: List[T = A], ?b: Int64) :- src(?a, ?b)",
        ),
        (
            "ub_sigilfree",
            "rule g[A](a: List[T = A], b: Int64) :- src(a, b)",
        ),
    ] {
        crate::common::expect_load_errors(
            crate::common::try_load_kb_with(&list_src(ns, rule)),
            &["WI-582: rule type-variable `A` has no bounding guard"],
        );
    }
}

/// `domain` RESTRICTS — a bound with no nominal head is DECIDED, not suspended.
///
/// This row is about `typing::type_bound_verdict`, not about the introducer, and it is
/// the second thing this ticket changed. That predicate withheld a verdict whenever
/// either side was not a NOMINAL sort, which is a much wider set than "not determined":
/// an arrow and a tuple are fully determined types that `types_compatible` has arms for.
/// MEASURED before, on ground data with nothing undetermined anywhere — `?a` bound to a
/// concrete `[1, 2]`, its carried type `List[T = Int64]`, the bound written out — the
/// clause returned BOTH rows as conditional answers rather than rejecting either. Now it
/// rejects both, which is what a guard is for.
///
/// NO INTRODUCER APPEARS HERE: this is the CONCRETE spelling, so it isolates the
/// verdict change from everything else in this file.
#[test]
fn a_concrete_bound_with_no_nominal_head_restricts() {
    for (ns, rule) in [
        (
            "arrow_concrete",
            "rule g(?a: (Int64) -> Int64, ?b: Int64) :- src(?a, ?b)",
        ),
        (
            "tuple_concrete",
            "rule g(?a: (x: Int64), ?b: Int64) :- src(?a, ?b)",
        ),
    ] {
        let mut kb = crate::common::load_kb_with(&list_src(ns, rule));
        assert_eq!(
            answers(&mut kb, &format!("test.pw9a0.{ns}.ungated(?a, ?b)")),
            2,
            "{ns}: the FACTS admit both rows"
        );
        assert_eq!(
            answers(&mut kb, &format!("test.pw9a0.{ns}.g(?a, ?b)")),
            0,
            "{ns}: neither list is a function or a tuple — the guard must reject both, \
             where it used to hand both back as residuals"
        );
    }
}

/// THE OTHER HALF OF THAT PREDICATE, and the reason the row above cannot stand alone: a
/// fixture that can only REFUTE cannot tell a working guard from one that rejects
/// everything. A `(x: Int64)` bound over a table of TUPLES keeps its own row by value,
/// drops one whose FIELD type differs, and drops a non-tuple — three outcomes from one
/// bound, all of them previously a single suspended non-answer.
#[test]
fn and_it_holds_where_the_value_does_conform() {
    let mut kb = crate::common::load_kb_with(&table_src(
        "tuple_holds",
        "(x: 1)",
        "(x: true)",
        "rule g(?a: (x: Int64), ?b: Int64) :- src(?a, ?b)",
    ));
    assert_eq!(
        answers(&mut kb, "test.pw9a0.tuple_holds.ungated(?a, ?b)"),
        2
    );
    assert_eq!(
        answers(&mut kb, "test.pw9a0.tuple_holds.g(?a, 7)"),
        1,
        "`(x: 1)` conforms to `(x: Int64)` — HOLDS, which the old verdict never said"
    );
    assert_eq!(
        answers(&mut kb, "test.pw9a0.tuple_holds.g(?a, 8)"),
        0,
        "`(x: true)` differs in its FIELD type — refuted at depth, not at the head"
    );
}

/// A VARIABLE ONE LEVEL IN IS STILL A VARIABLE — and this row's NOMINAL half is the one
/// that was giving a WRONG ANSWER on mainline before any of this ticket's work.
///
/// `types_compatible`'s `type_var` arm is a WILDCARD returning `true`, so a bound
/// compared against a carried type whose CHILD is unknown succeeded on the wildcard and
/// the guard admitted a row it exists to reject. MEASURED on mainline, with a plain
/// nominal bound and nothing from this ticket in play: `rule nf(?x: List[T = Int64])`
/// queried as `nf([?y])` answered **2 DEFINITE** — both the `[1]` row and the `[true]`
/// row — where `nf(?x)` answers 1. The more general query returned MORE definite rows
/// than the ground one, which is not a missed suspension but a wrong answer.
///
/// It is fixed by asking the question DEEPLY rather than at the head: a type variable is
/// a perfectly GROUND term (`KnowledgeBase::value_is_ground` answers `true` for
/// `named_tuple(x: <type var>)`), so groundness is the wrong owner and the walk is its
/// own. The guard then DELAYS rather than deciding, rotation lets the body goal ground
/// the value, and it decides correctly — so the answer is definite and right, not a
/// residual.
///
/// Backing out `type_term_has_variable` gives 2 definite on BOTH halves; backing out the
/// whole verdict predicate gives 2 residuals on the tuple half and leaves the nominal
/// half at its mainline 2-definite. The nominal half therefore fails under a back-out of
/// this row's fix ALONE, which is what makes it evidence for the deep walk rather than
/// for anything else in this file.
#[test]
fn a_variable_one_level_in_is_still_a_variable() {
    const SRC: &str = r#"
namespace test.pw9a0.nested
  import anthill.prelude.{Int64, Bool, List}

  fact item((x: 1))
  fact item((x: true))
  fact lst([1])
  fact lst([true])

  rule f(?x: (x: Int64))        :- item(?x)
  rule nf(?x: List[T = Int64])  :- lst(?x)
  rule untyped(?x)              :- item(?x)
end
"#;
    let mut kb = crate::common::load_kb_with(SRC);
    // CONTROL: the facts admit both rows under no annotation.
    assert_eq!(answers(&mut kb, "test.pw9a0.nested.untyped(?x)"), 2);

    // The STRUCTURAL bound — this ticket's widening.
    assert_eq!(answers(&mut kb, "test.pw9a0.nested.f(?x)"), 1);
    assert_eq!(
        answers(&mut kb, "test.pw9a0.nested.f((x: ?y))"),
        1,
        "a partially-instantiated argument must not buy MORE rows than a bare variable \
         does: the guard delays on the unknown child and decides once it is ground"
    );
    assert_eq!(answers(&mut kb, "test.pw9a0.nested.f((x: true))"), 0);
    assert_eq!(answers(&mut kb, "test.pw9a0.nested.f((x: 1))"), 1);

    // The NOMINAL bound — untouched by the widening, and wrong on mainline.
    assert_eq!(answers(&mut kb, "test.pw9a0.nested.nf(?x)"), 1);
    assert_eq!(
        answers(&mut kb, "test.pw9a0.nested.nf([?y])"),
        1,
        "MAINLINE ANSWERED 2 HERE, including the `[true]` row — the wildcard admitted a \
         binding the bound rejects"
    );
    assert_eq!(answers(&mut kb, "test.pw9a0.nested.nf([true])"), 0);
}

/// THE INTRODUCER ARM of the row above: substituting a bounded type variable into an
/// arrow or a tuple gives the same verdict as writing a concrete type there. Two axes
/// meet in this row — back out the substitution and it fails at load with
/// `unresolved name 'A'`; back out the verdict predicate and it answers 2 residuals.
#[test]
fn so_does_one_with_an_introducer_substituted_into_it() {
    for (ns, rule) in [
        (
            "arrow_tvar",
            "rule g[A](?a: (A) -> Int64, ?b: Int64) :- src(?a, ?b), Summable[A]",
        ),
        (
            "tuple_tvar",
            "rule g[A](?a: (x: A), ?b: Int64) :- src(?a, ?b), Summable[A]",
        ),
    ] {
        let mut kb = crate::common::load_kb_with(&list_src(ns, rule));
        assert_eq!(
            answers(&mut kb, &format!("test.pw9a0.{ns}.ungated(?a, ?b)")),
            2
        );
        assert_eq!(answers(&mut kb, &format!("test.pw9a0.{ns}.g(?a, ?b)")), 0);
    }
}
