//! WI-20260920-XSVCS — AN OPERATION-LEVEL `requires` FORWARDED THROUGH A GENERIC CALLER
//! IS CHECKED AT THE CALL.
//!
//! `mid[U](y: U) = tyOf(y)`, where `tyOf[B](x: B) requires TT[T = B]`, hands its own
//! rigid to an operation that demands evidence about it while holding none and having
//! declared none. Before this ticket the program LOADED CLEAN and died at run time with
//! `EvalError::Internal("DeferToRequirement: … `__req_tt` not bound in caller frame")` —
//! not a `Raised` payload, so no handler sees it, and in a debug build an ABORT through
//! `bridge_op_to_eval`'s `debug_assert`, from a program the typer accepted.
//!
//! THE REFUSAL IS A PARK, NOT A RAISE, and WI-20260921-3G1YT left that true for ONE
//! reason where there were two. [`caller_rigid_carrier`] answers "nothing can ever fill
//! this slot" from the call site's σ, which is alive only here; the refusal is REPORTED
//! by `report_unsuppliable_requirements` once every body is typed, because an operation
//! is routinely called before its own body is classified. What is GONE is the second
//! half: the park is no longer decided against "does the callee's body read it?", so a
//! declared clause is owed whether or not the callee currently uses it — see
//! [`the_same_forward_is_refused_whichever_body_the_callee_has`], the two bodies side by
//! side, and [`deleting_the_clause_the_body_never_uses_is_the_repair`], which is the way
//! out for the callee that does not.
//!
//! BACK-OUTS — each a MUTATION RUN on its own over the whole `wi_tests` binary (4828
//! rows), never a deletion and never a count guessed from reading:
//!
//! * **the rule off** — `caller_rigid_carrier` returning `None` unconditionally, so an
//!   unfilled rigid-carrier slot goes back to being a silent absence: **4 red** when this
//!   file was written, exactly the four the census predicted —
//!   [`a_forward_of_the_callers_own_rigid_is_refused_at_the_call`],
//!   [`the_corpus_instance_wi416_is_refused_and_the_clause_repairs_it`],
//!   [`the_printed_repair_loads_and_answers`], and
//!   `wi_n31xx_type_value_read_rule_test::a_middle_level_that_drops_the_clause_is_
//!   refused_at_the_call`'s plain-spec half. Measured again over the whole binary since
//!   (7335 rows): **11 red** — those four, [`the_same_forward_is_refused_whichever_body_the_callee_has`],
//!   the two rows of a rigid inside an application below, three of
//!   `wi_xqgew_member_param_test` (`a_forward_over_a_member_is_told_the_spelling_that_works`,
//!   `a_member_in_a_later_binding_takes_the_members_repair`,
//!   `every_member_of_the_spec_moves_to_the_bracket`) and
//!   `spec_op_requirement_at_member_test::a_call_whose_member_is_chosen_later_owes_the_spec_operations_requirement`
//!   — each a forward written after the census.
//! * **the reading of an application off** — `caller_writeable_application` answering
//!   `None`, so a rigid inside a sort application is not read: **2 red**, the two rows of
//!   it below, and nothing else in the binary moves.
//! * **the READ gate off** — `report_unsuppliable_requirements` reporting every parked
//!   op-slot refusal without consulting the body: **5 red** when this file was written,
//!   and WI-20260921-3G1YT then took that measurement as its instruction. The gate is
//!   DELETED, and all five rows are repaired rather than protected: each was a callee
//!   declaring a clause its body ignores, and the repair for such a callee is to delete
//!   the clause. The four that were not this ticket's —
//!   `wi1102…::control_a_body_that_never_reads_the_slot_still_runs`,
//!   `wi1119…::a_candidate_the_call_cannot_reach_is_not_half_of_a_tie`,
//!   `wi201…::bare_spec_member_param_infers_at_concrete_call` and
//!   `wi855…::other_unresolvable_causes_still_enter_unsupplied` — say so at their own
//!   sites. So "declared and never read must keep loading" was never a rule: it was the
//!   shape of the excuse, and four rows had been written against it.
//! * **the sort-parameter half of [`caller_param_rigids`] off** (op brackets only):
//!   **1 red**, [`the_corpus_instance_wi416_is_refused_and_the_clause_repairs_it`] — its
//!   carrier is `Coll`'s own `T`, not an operation bracket, so the lookup misses, no
//!   caller parameter matches, and the whole refusal is withheld.
//!
//! NOT MEASURED HERE, and said rather than left to be discovered: the writeability gate
//! in [`caller_rigid_carrier`] — every binding must be a caller parameter, a ground type
//! or a sort applied to such, or no clause is printed and no refusal is parked. Backing it out is **0 red**,
//! because the census found no dep of that shape in the corpus and one cannot be built
//! out of a single-parameter spec. It is there so the printed repair is pastable by
//! CONSTRUCTION rather than by the luck of every live spec having one element; a row
//! for it needs a two-parameter spec forwarded with one element unnameable, which is a
//! fixture this ticket did not find a legal spelling for.
//!
//! PASSES EITHER WAY BY DESIGN — one control, stated at its site:
//! [`the_stdlib_still_loads`]. The repaired halves of the rows above do NOT belong in
//! that list: a caller that declares the clause has always loaded, but what those rows
//! assert is the ANSWER it then produces, which says the refusal is about a missing
//! supply and not about the shape `mid[U](y: U) = tyOf(y)` being banned.

use anthill_core::eval::Value;
use anthill_core::persistence::print::TermPrinter;

use crate::common::{interp_for, load_stdlib_kb, try_load_kb_with};

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

/// The repair the refusal PRINTS, read back out of it as `(clause, declaration)`.
///
/// THE POINT OF READING IT RATHER THAN RETYPING IT: the acceptance is that the message
/// names "the clause to add", and a test that writes its own well-formed clause measures
/// the CHECK and not the MESSAGE — it stays green while the printed advice drifts into
/// something that does not parse, or names the callee's formal, or points at the wrong
/// declaration. Here the rows below paste exactly what an author would paste.
fn printed_repair(err: &str) -> (String, String) {
    let (_, rest) = err.split_once("Declare `").unwrap_or_else(|| {
        panic!("the refusal must print a repair beginning ``Declare `requires …```; got {err:?}")
    });
    let (clause, rest) = rest.split_once("` on `").unwrap_or_else(|| {
        panic!("the repair must name the declaration it goes on; got {err:?}")
    });
    let (declaration, _) = rest
        .split_once('`')
        .unwrap_or_else(|| panic!("unterminated declaration name; got {err:?}"));
    (clause.to_owned(), declaration.to_owned())
}

/// The ticket's own program. `tyOf` demands `TT[T = B]` and READS it (`TT.valueOf()` is
/// body-less on `TT`, so the call can only go through the slot); `mid` forwards its own
/// `U` into it and declares nothing.
///
/// `direct` is in the fixture on purpose: it calls the SAME operation with a carrier
/// this call pins (`Boom`, which provides `TT`), so Strategy 3 constructs the dictionary
/// and the call is fine. A rule that refused `tyOf` per se would take `direct` with it.
const FORWARD: &str = r#"
namespace test.xsvcs.fwd
  import anthill.prelude.{Type, String}

  sort TT
    import anthill.prelude.Type
    sort T = ?
    operation valueOf() -> Type
  end

  sort Boom
    import anthill.prelude.String
    entity boom(why: String)
    provides TT[T = Boom]
    operation valueOf() -> Type = Boom
  end

  operation tyOf[B](x: B) -> Type requires TT[T = B] = TT.valueOf[T = B]()
  operation mid[U](y: U) -> Type = tyOf(y)
  operation direct() -> Type = tyOf(boom(why: "x"))
  operation viaMid() -> Type = mid(boom(why: "x"))
end
"#;

#[test]
fn a_forward_of_the_callers_own_rigid_is_refused_at_the_call() {
    let errs = load_errors(FORWARD);
    assert_eq!(errs.len(), 1, "exactly one refusal, got {errs:#?}");
    let e = &errs[0];
    for want in [
        // THE CALLEE and the demand it makes, in the CALLER's spelling — `T = U`, not
        // the callee's own formal `T = test.xsvcs.fwd.tyOf.B`, which is a parameter of a
        // declaration the author of `mid` does not own.
        "cannot be supplied for call to `test.xsvcs.fwd.tyOf`",
        "test.xsvcs.fwd.TT[T = U]",
        // THE CALLER, which is the thing that is wrong: `tyOf`'s own declaration is
        // well-formed.
        "type parameter of the CALLING operation `test.xsvcs.fwd.mid`",
        // AND THE REPAIR, naming the declaration the clause goes on.
        "Declare `requires test.xsvcs.fwd.TT[T = U]` on `test.xsvcs.fwd.mid`",
    ] {
        assert!(e.contains(want), "expected {want:?} in the refusal; got {e:?}");
    }
    // LOCATED AT THE CALL inside `mid` (the fixture's nineteenth line), not at `tyOf`'s
    // declaration on the eighteenth and not at `viaMid`'s call of `mid`: the call that
    // cannot supply what it must is the one written in `mid`'s body.
    assert!(
        e.starts_with("19:"),
        "the refusal belongs at the forwarding call; got {e:?}"
    );
}

/// THE REPAIR THE MESSAGE PRINTS IS A REPAIR — pasted verbatim, loaded, and DRIVEN to
/// the answer the forward could not produce before.
///
/// This is also the row that pins the fault the ticket replaces. `viaMid` is the call
/// that used to load clean and die `EvalError::Internal("DeferToRequirement: …
/// `__req_tt` not bound in caller frame")` — uncatchable, and a debug-build abort one
/// frame on. With the clause the message asks for, it answers `Boom`.
#[test]
fn the_printed_repair_loads_and_answers() {
    let errs = load_errors(FORWARD);
    assert_eq!(errs.len(), 1, "exactly one refusal, got {errs:#?}");
    let (clause, declaration) = printed_repair(&errs[0]);
    assert_eq!(declaration, "test.xsvcs.fwd.mid");
    let repaired = FORWARD.replace(
        "operation mid[U](y: U) -> Type = tyOf(y)",
        &format!("operation mid[U](y: U) -> Type {clause} = tyOf(y)"),
    );
    assert_eq!(
        load_errors(&repaired),
        Vec::<String>::new(),
        "the clause the refusal printed must be the one that discharges it"
    );
    // BOTH CALLS ANSWER, and both answers are asserted: the direct one was never the
    // defect, and a fix that silently cost it its dictionary would show up here.
    assert_eq!(eval_type(&repaired, "test.xsvcs.fwd.direct"), "Boom");
    assert_eq!(eval_type(&repaired, "test.xsvcs.fwd.viaMid"), "Boom");
}

/// WI-20260921-3G1YT — **A CALLEE'S BODY NO LONGER DECIDES ITS CALLERS' OBLIGATIONS**,
/// and this is the row that says so: ONE signature, TWO bodies, side by side, and `mid`
/// is refused against BOTH.
///
/// **THIS ROW INVERTED.** It read `a_slot_the_callee_never_reads_still_loads_and_answers`
/// and asserted the second body LOADS — the control for a READ GATE that asked whether
/// `tyOf`'s *present* body happens to touch its `TT` slot. That gate, and the two body
/// walks behind it, are deleted. The two programs differ only in text inside `tyOf` that
/// `mid`'s author does not own and cannot see from the call; admitting the caller on it
/// means the caller breaks when the callee's body changes, with nothing at the call site
/// having moved. That was the ticket's defect (1), and this file's own fixture was its
/// sharpest statement.
///
/// The verdict is identical to that of
/// [`a_forward_of_the_callers_own_rigid_is_refused_at_the_call`] because it IS the same
/// verdict: `mid[U](y: U) = tyOf(y)` forwards its own rigid into an operation that
/// demands evidence about it, declaring none and holding none. Both halves are asserted
/// here rather than by pointing at that row, because what this one measures is that the
/// two bodies give the SAME answer.
#[test]
fn the_same_forward_is_refused_whichever_body_the_callee_has() {
    let never_read = FORWARD.replace(
        "operation tyOf[B](x: B) -> Type requires TT[T = B] = TT.valueOf[T = B]()",
        "operation tyOf[B](x: B) -> Type requires TT[T = B] = Boom",
    );
    assert_ne!(never_read, FORWARD, "the fixture edit must have applied");
    for (which, src) in [("reads the slot", FORWARD), ("never reads it", &never_read)] {
        let errs = load_errors(src);
        assert_eq!(errs.len(), 1, "{which}: exactly one refusal, got {errs:#?}");
        assert!(
            errs[0].contains("cannot be supplied for call to `test.xsvcs.fwd.tyOf`")
                && errs[0].contains("test.xsvcs.fwd.TT[T = U]"),
            "{which}: the refusal must name the callee and the demand; got {:?}",
            errs[0]
        );
    }
}

/// AND THE REPAIR FOR A CLAUSE THE BODY DOES NOT USE IS TO **DELETE IT**, not to weaken
/// the rule — driven, because an acceptance that only asserts a new refusal leaves the
/// author of such a callee with no way out.
///
/// This is the other half of the row above. A `tyOf` that answers a constant has no use
/// for `TT` evidence; the clause was noise, and the walk that used to excuse it was the
/// only thing making the noise free. With the clause gone the program loads and BOTH
/// calls answer — `direct`, which was never the defect, and `viaMid`, which is the
/// forward.
///
/// THE POPULATION THE WALKS EXISTED FOR IS NOT REPAIRED THIS WAY, and saying so is the
/// point: their justification was 29 stdlib bodies that declare a chain and never read
/// it, and not one of them needed an excuse. The stdlib loads clean with both walks gone
/// ([`the_stdlib_still_loads`]) because those calls are DISCHARGED by route 4 —
/// `scope_contract_covers_dep`, the caller holding a spec-typed value — rather than
/// excused by a walk of someone else's body.
#[test]
fn deleting_the_clause_the_body_never_uses_is_the_repair() {
    let repaired = FORWARD.replace(
        "operation tyOf[B](x: B) -> Type requires TT[T = B] = TT.valueOf[T = B]()",
        "operation tyOf[B](x: B) -> Type = Boom",
    );
    assert_ne!(repaired, FORWARD, "the fixture edit must have applied");
    assert_eq!(
        load_errors(&repaired),
        Vec::<String>::new(),
        "a callee that declares no evidence demands none, and its callers owe nothing"
    );
    assert_eq!(eval_type(&repaired, "test.xsvcs.fwd.direct"), "Boom");
    assert_eq!(eval_type(&repaired, "test.xsvcs.fwd.viaMid"), "Boom");
}

/// THE INSTANCE NOBODY WROTE AS A TEST — found by the census this ticket's first step
/// ran, in `anthill-cli`'s own WI-416 fixture, where it has loaded clean since 2025.
///
/// `Coll.contains` calls `List.contains(items, x)` on its own `T`. `List.contains`
/// declares `requires Eq[T]` and its body READS it (`eq(head, x)`), so the call needs a
/// dictionary for `Eq[Coll.T]` — which `Coll` declares nothing about. Anything that
/// called `Coll.contains` would have died `Internal`; nothing ever did, which is exactly
/// how a silent class stays silent.
///
/// THE CARRIER IS A SORT PARAMETER, not an operation bracket, and that is what this row
/// measures that the others do not: the repair names `test.wi416.Coll`, the SORT, since
/// an operation cannot declare its sort's parameter out from under it.
#[test]
fn the_corpus_instance_wi416_is_refused_and_the_clause_repairs_it() {
    let src = r#"
namespace test.wi416
  import anthill.prelude.{List, Int64, Bool}

  sort Coll
    sort T = ?
    operation contains(items: List[T], x: T) -> Bool = List.contains(items, x)
  end
end
"#;
    let errs = load_errors(src);
    assert_eq!(errs.len(), 1, "exactly one refusal, got {errs:#?}");
    let e = &errs[0];
    for want in [
        "cannot be supplied for call to `anthill.prelude.List.contains`",
        "type parameter of the CALLING operation `test.wi416.Coll.contains`",
    ] {
        assert!(e.contains(want), "expected {want:?} in the refusal; got {e:?}");
    }

    // THE REPAIR NAMES THE SORT, not the operation whose body wrote the call: `T` is
    // `Coll`'s parameter and `contains` cannot declare it out from under it.
    let (clause, declaration) = printed_repair(e);
    assert_eq!(declaration, "test.wi416.Coll");

    // AND THE CLAUSE IT PRINTS MAKES THE PROGRAM LOAD. Without this half the row would
    // assert only that something is now refused, which is satisfied by refusing it for
    // the wrong reason.
    let repaired = src.replace(
        "  sort Coll\n    sort T = ?",
        &format!("  sort Coll\n    {clause}\n    sort T = ?"),
    );
    assert_ne!(repaired, src, "the fixture edit must have applied");
    assert_eq!(
        load_errors(&repaired),
        Vec::<String>::new(),
        "the clause the refusal asks for must be the one that discharges it"
    );
}

/// A RIGID INSIDE A SORT APPLICATION IS FORWARDED TOO. `tyOf(some(x))` over `x: C` hands
/// `Option[T = C]` to an operation that demands evidence about it, and `Option`'s instance
/// holds only where `C`'s does, which `f` holds none of. It loaded clean, and reached from a
/// query it panicked "`__req_typevalue` not bound in caller frame"; a bare `tyOf(x)` was
/// already refused. Refused now, naming the evidence the caller lacks: `TypeValue` at the
/// parameter itself, since the library's instances are derived per type argument.
///
/// BACK-OUT: the reading of an application (`caller_writeable_application`) answering
/// `None`, and the program loads clean again; with the forward rule off as a whole, the
/// same.
const NESTED: &str = r#"
namespace test.xsvcs.nested
  import anthill.prelude.{Int64, Option, Type}
  import anthill.prelude.Option.{some}
  import anthill.reflect.{TypeValue}
  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = TypeValue.type_value[T = B]()
  operation f[C](x: C) -> Type = tyOf(some(x))
  operation viaF() -> Type = f(1)
end
"#;

#[test]
fn a_rigid_inside_an_application_is_refused_and_the_printed_repair_answers() {
    let errs = load_errors(NESTED);
    assert_eq!(errs.len(), 1, "exactly one refusal, got {errs:#?}");
    let e = &errs[0];
    for want in [
        "`anthill.reflect.TypeValue[T = anthill.prelude.Option[T = C]]` cannot be supplied for \
         call to `test.xsvcs.nested.tyOf`",
        "its carrier `anthill.prelude.Option[T = C]` holds `C`, a type parameter of the \
         CALLING operation `test.xsvcs.nested.f`",
    ] {
        assert!(e.contains(want), "expected {want:?} in the refusal; got {e:?}");
    }
    let (clause, declaration) = printed_repair(e);
    assert_eq!(clause, "requires anthill.reflect.TypeValue[T = C]");
    assert_eq!(declaration, "test.xsvcs.nested.f");
    let repaired = crate::common::replace_in_fixture(
        NESTED,
        "operation f[C](x: C) -> Type = tyOf(some(x))",
        &format!("operation f[C](x: C) -> Type {clause} = tyOf(some(x))"),
    );
    assert_eq!(load_errors(&repaired), Vec::<String>::new());
    assert_eq!(eval_type(&repaired, "test.xsvcs.nested.viaF"), "Option(T: Int64)");
}

/// And over a spec of the program's own, provided at `Box` on the condition of its element
/// (`Quiet requires Desc[T = E]`, `provides Desc[T = Box[B = E]]`): the clause printed is the
/// requirement as the call states it, which a caller can hold whatever the provision's
/// condition is, and pasted it answers through `Quiet`'s row.
///
/// BACK-OUT: as the row above.
const NESTED_OWN: &str = r#"
namespace test.xsvcs.nestedown
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Box
    sort B = ?
    entity box(inner: B)
  end
  sort IntDesc
    provides Desc[T = Int64]
    operation describe(x: Int64) -> Int64 = 1
  end
  sort Quiet
    sort E = ?
    requires Desc[T = E]
    provides Desc[T = Box[B = E]]
    operation describe(b: Box[B = E]) -> Int64 = 5
  end
  sort Reader
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[T = HT] = Desc.describe(x)
  end
  operation fwd[C](x: C) -> Int64 = Reader.probe(box(inner: x))
  operation go() -> Int64 = fwd(3)
end
"#;

#[test]
fn a_rigid_inside_an_application_of_a_programs_spec_is_refused_too() {
    let errs = load_errors(NESTED_OWN);
    assert_eq!(errs.len(), 1, "exactly one refusal, got {errs:#?}");
    let e = &errs[0];
    assert!(
        e.contains(
            "its carrier `test.xsvcs.nestedown.Box[B = C]` holds `C`, a type parameter of the \
             CALLING operation `test.xsvcs.nestedown.fwd`"
        ),
        "{e}"
    );
    let (clause, declaration) = printed_repair(e);
    assert_eq!(
        clause,
        "requires test.xsvcs.nestedown.Desc[T = test.xsvcs.nestedown.Box[B = C]]"
    );
    assert_eq!(declaration, "test.xsvcs.nestedown.fwd");
    let repaired = crate::common::replace_in_fixture(
        NESTED_OWN,
        "operation fwd[C](x: C) -> Int64 = Reader.probe(box(inner: x))",
        &format!("operation fwd[C](x: C) -> Int64 {clause} = Reader.probe(box(inner: x))"),
    );
    assert_eq!(load_errors(&repaired), Vec::<String>::new());
    let mut interp = interp_for(&repaired);
    let v = interp.call("test.xsvcs.nestedown.go", &[]).expect("go runs");
    assert_eq!(
        anthill_core::kb::term_view::TermView::literal_int64(&v, interp.kb()),
        Some(5)
    );
}

/// THE STDLIB STILL LOADS — asserted rather than assumed, because the population this
/// rule had to avoid lives there. `load_stdlib_kb` panics on any load error, so this is
/// a real assertion and not a smoke test; the census counted 57 unfilled op slots across
/// the workspace and this rule touches only the ones that name a caller rigid.
///
/// PASSES EITHER WAY BY DESIGN: the control the module doc names.
#[test]
fn the_stdlib_still_loads() {
    let kb = load_stdlib_kb();
    // NAMED, not counted: a KB that loaded nothing would satisfy the panic-free half
    // vacuously, and the one symbol worth asking for is the operation this rule's own
    // corpus instance calls.
    assert!(
        kb.try_resolve_symbol("anthill.prelude.List.contains").is_some(),
        "the stdlib must still carry the requirement-declaring operation itself"
    );
}
