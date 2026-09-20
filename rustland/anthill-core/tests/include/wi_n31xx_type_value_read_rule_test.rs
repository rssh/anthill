//! WI-20260919-N31XX (proposal 065, "The rule") — A RIGID TYPE IS A VALUE ONLY WHERE A
//! REQUIREMENT SAYS SO.
//!
//! TWO HALVES, and the second is not decoration. The READ half refuses
//! `operation bad[B](x: B) -> Type = Cell[V = B]`, which inspects `B` without saying so.
//! The FORWARD half refuses `mid[U](y: U) = tyOf(y)`, which inspects nothing but hands
//! its own rigid to an operation that does, holding no evidence and having declared none.
//! With only the first, a signature could still quietly depend on a type it promises
//! nothing about — see [`a_middle_level_that_drops_the_clause_is_refused_at_the_call`].
//!
//! `operation bad[B](x: B) -> Type = Cell[V = B]` reads `B` in VALUE position. Under 065
//! that is a LOAD error unless `TypeValue[T = B]` stands among the requirements in scope,
//! and the refusal names the parameter, the read's line and column, and the clause to
//! add. The point is not tidiness: without it a signature `f[B](x: B) -> R` promises
//! nothing about whether `f` inspects `B`, so parametricity is false, a provider's own
//! parameter entered through a slot has no call site that could supply it, and an
//! erasing backend has nothing to read (065's opening paragraph).
//!
//! BACK-OUTS — each a MUTATION run on its own (the site still runs, its answer is
//! discarded), never a deletion, and each count is of a run over this file plus the five
//! census files the migration touched:
//!
//! * **the rule off** — the `TypeValueReadUnbacked` push in `check_operation_bodies`
//!   neutralized: **1 red**, [`a_value_read_with_no_clause_is_refused`]. Nothing else in
//!   any of the six files moves, and that isolation is the point — it says the migration
//!   added clauses that were NEEDED and not clauses that merely silenced something.
//!   [`the_operation_level_subset_rule_is_065_3`] stays green: `check_override_refinement`
//!   is a separate leg, so that row measures §3 and this rule independently.
//! * **the clause reader's op-level half off** — `type_value_backed_params` reads only
//!   `direct_requires`: **31 red across the six files, 4 of them here** —
//!   [`the_clause_admits_the_read_and_the_answer_is_the_ground_type`],
//!   [`the_clause_reaches_through_two_generic_levels`],
//!   [`a_middle_level_that_drops_the_clause_still_loads_today`] and
//!   [`a_simp_expanded_type_position_is_not_a_value_read`], because every clause in this
//!   file that admits a read is written on an OPERATION. MEASURED, and it was the first
//!   cut's actual defect: an op-level clause arrives as the bare application the author
//!   wrote, not as a `SortView`, and `unwrap_spec_view_value` answers "no bindings" for
//!   it — so `operation ty[T]() -> Type requires TypeValue[T = T]` was refused with its
//!   own clause written two columns away.
//! * **the FORWARD leg off** — the `TypeValue` arm in `build_op_scoped_dicts` removed,
//!   so an unsuppliable op slot goes back to being a silent absence: **1 red**,
//!   [`a_middle_level_that_drops_the_clause_is_refused_at_the_call`]. Its plain-spec
//!   half stays green either way, which is what says the leg is narrow on purpose.
//! * **the post-simp placement off** — the rule reading `op.body_node` (the tree the
//!   typer was handed) instead of `result.node` (the tree it wrote back): **2 red** —
//!   [`a_simp_expanded_type_position_is_not_a_value_read`] and, in the census file
//!   itself, `wi_h054k_type_position_subst_test::a_binding_that_denotes_no_type_is_bottom_and_says_so`.
//!   That second one is why the placement is the rule and not a detail: 065 §6's
//!   nineteenth site is a real program in the corpus, and judging it before `@[simp]`
//!   inlining refuses it for a `K` that only ever reaches a TYPE position.
//!
//! PASS EITHER WAY BY DESIGN — controls, stated at their sites:
//! [`a_type_position_read_needs_no_clause`],
//! [`a_concrete_sort_in_value_position_needs_no_clause`].

use anthill_core::eval::Value;
use anthill_core::persistence::print::TermPrinter;

use crate::common::{interp_for, try_load_kb_with};

fn load_errors(src: &str) -> Vec<String> {
    match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    }
}

fn eval_type(src: &str, op: &str) -> String {
    let mut interp = interp_for(src);
    match interp.call(op, &[]) {
        Ok(Value::Term { id, .. }) => TermPrinter::new(interp.kb()).print_term(id),
        Ok(other) => panic!("{op}: expected a term-carried type, got {other:?}"),
        Err(e) => panic!("{op}: {e:?}"),
    }
}

// ── THE RULE ─────────────────────────────────────────────────────────────────────────

/// 065's own example, refused with 065's own message. The `-> Type` return is what makes
/// this a VALUE read and not a type one: `B` is the thing being produced.
#[test]
fn a_value_read_with_no_clause_is_refused() {
    let errs = load_errors(
        r#"
namespace test.n31xx.bad
  import anthill.prelude.{Cell, Type}

  operation bad[B](x: B) -> Type = Cell[V = B]
end
"#,
    );
    assert_eq!(errs.len(), 1, "exactly one refusal, got {errs:#?}");
    let e = &errs[0];
    // THE PARAMETER, THE CLAUSE TO ADD, AND THE OPERATION THAT MUST CARRY IT — a
    // refusal that named only "a type parameter is read as a value" would leave the
    // author to work out which one and where the clause goes.
    for want in [
        "`B` is read as a VALUE",
        "anthill.reflect.TypeValue[T = B]",
        "test.n31xx.bad.bad",
    ] {
        assert!(e.contains(want), "expected {want:?} in the refusal; got {e:?}");
    }
    // AND THE READ'S LINE AND COLUMN, which 065 asks for by name. The read is on the
    // fixture's fifth line; the column is the `B` inside `Cell[V = B]`, not the
    // operation's own line, because the repair is read at the signature but the FAULT is
    // at the read.
    assert!(
        e.starts_with("5:"),
        "the refusal must be located at the read's line; got {e:?}"
    );
}

/// THE CONTROL, and it asserts the ANSWER and not merely that the program loads: the
/// clause must admit the read AND leave the value the read delivers intact. One generic
/// level — the caller pins `B` at the call site.
#[test]
fn the_clause_admits_the_read_and_the_answer_is_the_ground_type() {
    let src = r#"
namespace test.n31xx.one
  import anthill.prelude.{Cell, Int64, String, Type}
  import anthill.reflect.{TypeValue}

  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]

  operation ask_int() -> Type = tyOf(5)
  operation ask_str() -> Type = tyOf("s")
end
"#;
    assert_eq!(eval_type(src, "test.n31xx.one.ask_int"), "Cell(V: Int64)");
    // The SECOND instantiation is not decoration: a single row cannot tell a correct
    // answer from a first binding that leaked.
    assert_eq!(eval_type(src, "test.n31xx.one.ask_str"), "Cell(V: String)");
}

/// …and THROUGH TWO GENERIC LEVELS, which is where the rule earns its keep: the middle
/// operation has to declare the clause too, because it passes its own rigid down. That
/// propagation IS 065's parametricity claim — an operation that cannot name the evidence
/// cannot hand it on.
#[test]
fn the_clause_reaches_through_two_generic_levels() {
    let src = r#"
namespace test.n31xx.two
  import anthill.prelude.{Cell, Int64, Type}
  import anthill.reflect.{TypeValue}

  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]
  operation mid[U](y: U) -> Type requires TypeValue[T = U] = tyOf(y)

  operation ask() -> Type = mid(5)
end
"#;
    assert_eq!(eval_type(src, "test.n31xx.two.ask"), "Cell(V: Int64)");
}

/// …AND A MIDDLE LEVEL THAT DROPS THE CLAUSE IS REFUSED AT THE CALL — the FORWARD half
/// of the rule, which the read half above does not cover.
///
/// `mid[U](y: U) = tyOf(y)` reads nothing; it hands its own rigid to an operation that
/// `requires TypeValue[T = U]`, holding no evidence and having declared none. Without
/// this the rule would cover the READ and not the FORWARD, and a signature could still
/// quietly depend on a type it promises nothing about — parametricity half enforced.
///
/// WHY IT IS REFUSED RATHER THAN LEFT AS AN UNFILLED SLOT. `build_op_scoped_dicts` makes
/// an unsuppliable op slot a SILENT ABSENCE on purpose, and its own comment gives the
/// measured reason: 29 stdlib bodies declare a chain and never read it, so a slot nothing
/// fills costs them nothing. `TypeValue` can never be one of those — `type_value()` is
/// NULLARY, so no argument and no receiver names the type and the dispatching dictionary
/// is the ONLY carrier of the answer (WI-20260919-HXGXF's fact 1). A body holding this
/// evidence necessarily reads it through the slot, so an unfilled one is either an
/// eval-time `Internal` death no handler can catch or a clause that was pure noise.
///
/// AT THE CALL, NOT AT THE DECLARATION: `mid`'s signature is legal on its own, and it is
/// only this call that needs what `mid` has not got. The refusal is located there.
///
/// THE SECOND HALF IS THE CONTROL AND IT STILL LOADS. The same forward shape over a
/// plain user spec — `requires TT[T = B]`, nothing to do with 065 — is accepted, because
/// this leg is deliberately narrow: it says `TypeValue` evidence is never benignly
/// absent, NOT that operation-level requirement propagation is now checked in general.
/// That wider gap is real and pre-existing, and is not this ticket's to close; without
/// this row a later reader would have no way to tell the two apart.
#[test]
fn a_middle_level_that_drops_the_clause_is_refused_at_the_call() {
    let type_value = load_errors(
        r#"
namespace test.n31xx.twobad
  import anthill.prelude.{Cell, Int64, Type}
  import anthill.reflect.{TypeValue}

  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]
  operation mid[U](y: U) -> Type = tyOf(y)

  operation ask() -> Type = mid(5)
end
"#,
    );
    assert_eq!(type_value.len(), 1, "exactly one refusal, got {type_value:#?}");
    let e = &type_value[0];
    for want in [
        "anthill.reflect.TypeValue",
        "cannot be supplied for call to",
        "test.n31xx.twobad.tyOf",
        "only by the dispatching dictionary",
    ] {
        assert!(e.contains(want), "expected {want:?} in the refusal; got {e:?}");
    }
    // LOCATED AT THE CALL inside `mid` (the fixture's seventh line), not at `tyOf`'s
    // declaration on the sixth: `tyOf` is well-formed, and the caller is what is wrong.
    assert!(
        e.starts_with("7:"),
        "the refusal belongs at the forwarding call; got {e:?}"
    );

    // THE CONTROL — the same shape over a plain spec, still accepted. See the doc above.
    let plain_spec = load_errors(
        r#"
namespace test.n31xx.othersp
  import anthill.prelude.{Type, Int64}

  sort TT
    import anthill.prelude.Type
    sort T = ?
    operation valueOf() -> Type
  end

  operation tyOf[B](x: B) -> Type requires TT[T = B] = TT.valueOf()
  operation mid[U](y: U) -> Type = tyOf(y)
  operation ask() -> Type = mid(5)
end
"#,
    );
    assert_eq!(
        plain_spec,
        Vec::<String>::new(),
        "this leg is narrow by design: it does not close operation-level requirement \
         propagation in general, and that wider gap is pre-existing"
    );
}

// ── 065 §3, THE OPERATION-LEVEL SUBSET RULE ──────────────────────────────────────────

/// AN IMPLEMENTATION MAY NOT ADD AN OPERATION-LEVEL CLAUSE, AND MAY ADD AN INSTANCE ONE.
///
/// 065 §3's table in one program. An operation-level `requires` is an extra INPUT the
/// caller supplies per call, and a caller dispatching through the spec knows only the
/// spec's signature — so `Box.valueOf requires TypeValue[T = V]` is refused. The SAME
/// evidence written on the SORT rides the instance, which the spec's caller never sees,
/// and loads.
///
/// MEASURED, not reasoned: this is the refusal the r541x migration actually hit, and
/// moving the clause from the operation to the sort is what cleared it.
///
/// TWO INDEPENDENT LEGS, so this row is not a duplicate of part 1's: part 1 made a
/// RESTATED clause load (`check_override_refinement`'s type-parameter alignment); this
/// asserts that an ADDED one still does not.
#[test]
fn the_operation_level_subset_rule_is_065_3() {
    const SPEC: &str = r#"
namespace test.n31xx.sub
  import anthill.prelude.{Type, String}
  import anthill.reflect.{TypeValue}

  sort TT
    import anthill.prelude.Type
    sort T = ?
    operation valueOf() -> Type
  end

  sort Boom
    entity boom(why: String)
  end

  sort Box
    import anthill.prelude.Type
    import anthill.reflect.{TypeValue}
    sort V = ?
    entity box(v: V)
@CLAUSE@
    provides TT[T = Box[V = V]]
    operation valueOf() -> Type @OPCLAUSE@= Box[V = V]
  end

  operation ask() -> Type = Box[V = Boom].valueOf()
end
"#;
    // (a) the OPERATION-level addition — refused.
    let added = SPEC.replace("@CLAUSE@\n", "").replace(
        "@OPCLAUSE@",
        "requires TypeValue[T = V] ",
    );
    let errs = load_errors(&added);
    assert!(
        errs.iter()
            .any(|e| e.contains("strengthens the precondition")),
        "an implementation may not ADD an operation-level clause the spec lacks; got {errs:#?}"
    );

    // (b) the INSTANCE-level spelling — loads, and answers.
    let instance = SPEC
        .replace("@CLAUSE@", "    requires TypeValue[T = V]")
        .replace("@OPCLAUSE@", "");
    assert_eq!(
        eval_type(&instance, "test.n31xx.sub.ask"),
        "Box(V: Boom)",
        "a clause over the provider's OWN parameter rides the instance and is permitted"
    );
}

// ── CONTROLS — green with or without the rule ────────────────────────────────────────

/// A TYPE POSITION IS NOT A READ. `x: B` and `-> List[T = B]` are static and erasable,
/// and nothing reads them at run time — 065's first exclusion. This operation mentions
/// `B` three times and carries no clause.
#[test]
fn a_type_position_read_needs_no_clause() {
    let src = r#"
namespace test.n31xx.typepos
  import anthill.prelude.{List, Int64}
  import anthill.prelude.List.{cons, nil}

  operation single[B](x: B) -> List[T = B] = cons(x, nil())
  operation ask() -> Int64 = 1
end
"#;
    assert_eq!(load_errors(src), Vec::<String>::new(), "no clause is needed");
    let mut interp = interp_for(src);
    // DRIVEN, not merely loaded: a signature-only assertion would stay green if the
    // operation resolved to nothing.
    assert!(matches!(
        interp.call("test.n31xx.typepos.ask", &[]),
        Ok(Value::Int(1))
    ));
}

/// A CONCRETE SORT IN VALUE POSITION READS NO RIGID — 065's second exclusion. Its
/// `TypeValue` is the derived instance, discharged statically at no cost to the author,
/// so `Cell[V = Int64]` as a value needs nothing declared.
#[test]
fn a_concrete_sort_in_value_position_needs_no_clause() {
    let src = r#"
namespace test.n31xx.concrete
  import anthill.prelude.{Cell, Int64, Type}

  operation ty() -> Type = Cell[V = Int64]
end
"#;
    assert_eq!(eval_type(src, "test.n31xx.concrete.ty"), "Cell(V: Int64)");
}

/// 065 §6's NINETEENTH CENSUS SITE, and the reason the rule is judged on the tree the
/// typer WROTE BACK rather than the one it was handed.
///
/// `dq[K]()` passes `K` as an ARGUMENT to a `@[simp]` equation whose RHS puts it in a
/// TYPE position. Before expansion `K` looks like a value read and the rule would refuse
/// a program whose only use of `K` is as a type; after expansion there is no value read
/// at all. `dq` therefore carries NO clause — that absence is the assertion.
///
/// THE CONTROL IS THE SECOND OPERATION, which reads `K` as a genuine value and does
/// carry the clause: without it this row would pass equally against a rule that never
/// fired in this file at all.
#[test]
fn a_simp_expanded_type_position_is_not_a_value_read() {
    let src = r#"
namespace test.n31xx.simp
  import anthill.prelude.{Map, Int64, String, Cell, Type}
  import anthill.prelude.Map.{put, size}
  import anthill.reflect.{TypeValue}

  rule mkq(?k) <=> Map[K = ?k, V = Int64].empty() @[simp]

  operation dq[K]() -> Int64 = size(put(mkq(K), "a", 1))
  operation genuine[K]() -> Type requires TypeValue[T = K] = Cell[V = K]

  operation ask() -> Int64 = dq[K = String]()
  operation ask_ty() -> Type = genuine[K = String]()
end
"#;
    assert_eq!(
        load_errors(src),
        Vec::<String>::new(),
        "a `K` that @[simp] inlining places in a TYPE position is not a value read"
    );
    let mut interp = interp_for(src);
    assert!(
        matches!(interp.call("test.n31xx.simp.ask", &[]), Ok(Value::Int(1))),
        "and the program still answers"
    );
    assert_eq!(
        eval_type(src, "test.n31xx.simp.ask_ty"),
        "Cell(V: String)",
        "the control: a genuine value read in the same file, under its clause"
    );
}
