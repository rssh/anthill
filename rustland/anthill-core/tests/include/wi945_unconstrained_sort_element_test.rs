//! WI-945 — a SORT-level requirement element NOTHING at the call pins is refused at
//! LOAD (§5.2), as the op-level twin of the same shape already was.
//!
//! THE DISAGREEMENT THE TICKET FOUND. `operation twice[V, F](a: V) -> V requires
//! VectorSpace[V, F]`, called as `twice(a)` at a `Vec3`, is refused at load —
//! `check_unconstrained_type_params` (WI-270) sees that the OPERATION's own `F` is
//! undetermined and says so. Move the very same declaration to the sort
//! (`sort V = ? / sort F = ? / requires VectorSpace[V, F]`) and WI-270 has nothing to
//! look at: sort parameters are not the operation's type parameters. That spelling
//! loaded clean and died `Internal(DeferToRequirement: requirement param
//! `__req_vectorspace` not bound in caller frame)` at eval — the clean-load-crash-at-run
//! shape §5.2 exists to forbid.
//!
//! WHERE THE HOLE WAS. `build_dispatching_dict_from_chain`'s `require_complete` arm
//! already raised WI-828's `RequirementRefusal` for two signatures: a σ-refused
//! covering entry, and an `Ambiguous` Strategy-3 construction. §5.2 names a third —
//! its diagnostic lists "the requirement, the unconstrained element, ANY σ-refused
//! covering entry, and the construction outcome", and that *any* is the case with
//! neither: a caller declaring no `requires` at all (nothing to refuse) whose
//! construction terminates `NoMatch` (nothing to tie). MEASURED: the subject below
//! reached `explain_dep_refusal` with `caller_requires = []` and `s3 = NoMatch`, so
//! both signatures declined and control fell to the silent `Ok(None)`.
//!
//! THE FIX IS NOT THE WIDENING THE TICKET PREDICTED, and the difference is the whole
//! content of this file. Raising on every unconstrained element flips four call-site
//! classes in the corpus, not one — measured by instrumenting the arm and running the
//! full workspace. Three of the four are CORRECT today and must stay:
//!
//!   1. the subject (`HolderVS.twice`) — dies at eval. REFUSE.
//!   2. `test.wi508g.useNew` (wi508) — `size(x)` on a `MutableStack`, `Element`
//!      unpinned, an OPERATION body, and it answers 1. `FiniteCollection.size`'s body
//!      (`List.length(collect(c))`) reads no `__req_*` at all, so the absent dictionary
//!      is an irrelevance. Pinned here by `control_a_callee_that_never_reads_the_slot`.
//!   3. `gap3b.combiner`'s `combines_to(?b, ?r)` (wi625 Layer B) — a RULE-body goal,
//!      whose dictionaries the SLD→eval bridge resolves from the CONCRETE argument
//!      values (`call_op_bridged` → `resolve_bridge_requirements`) and suspends when it
//!      cannot. An element unpinned at load is the ordinary case there, every goal
//!      argument being a variable. Pinned here by
//!      `control_a_rule_body_goal_is_supplied_by_the_bridge`.
//!   4. `PartialEq[T = PartialOrd.T]` at `anthill.prelude.PartialOrd` — a rule-body
//!      goal like (3), and the most common of the four: 89 of the 97 instrumented
//!      hits across the workspace.
//!
//! So the verdict needs two gates, each with a mechanism behind it: the call must be in
//! an OPERATION body (where the compile-built dictionary is the only supply), and the
//! CALLEE's body must actually read a sort-level slot. The second is WI-822 LEG 2's
//! rule one channel over — "has an unpinnable chain" and "needs it" are different
//! questions, and only the body answers the second — and it is why the refusal is
//! parked at the call site and decided in `report_unsuppliable_requirements`, after
//! both `check_operation_bodies` sweeps: an operation is routinely called before its
//! own body has been classified.
//!
//! "READS THE SLOT" COUNTS FIVE WAYS, and a first cut of this fix counted two. A body
//! DEFERS to a slot, INHERITS a frame (a same-sort call the typer built no dictionary
//! for), or FORWARDS — a call the typer DID build a dictionary for, one of whose slots
//! is a `var_ref` read of this frame rather than a construction. The third is the one
//! the two-way cut let through, and it loaded clean and died at eval exactly as the
//! subject did; see `a_forwarded_slot_inside_a_built_dictionary_is_refused_too`.
//!
//! THEN IT HAPPENED AGAIN, which is why the count is FIVE and not three: the three-way
//! cut this file shipped missed a forward through the OP-SCOPED half of the same
//! variant, and an ETA, each measured as the same clean load that dies at eval. They are
//! WI-1095's, driven by `wi1095_uncounted_frame_read_channels_test`, and the predicate's
//! `match` is exhaustive over `CallClass` now so a sixth is a compile error rather than
//! a silent `_ => Nothing`. Read that file before adding a fourth fixture here.
//!
//! WHAT EACH TEST HERE MEASURES, and what backing the change out costs:
//!  - `sort_level_unconstrained_element_is_refused_at_load` is the SUBJECT. It fails
//!    (loads clean) with the change reverted. It passes under a BLANKET raise too —
//!    which is exactly why the three controls below are the load-bearing half of this
//!    file: a blanket raise is the fix the ticket predicted, and only they refuse it.
//!  - `a_sibling_that_reads_the_slot_is_refused_too` is the subject one hop out. It
//!    fails (loads clean) if the verdict stops following same-sort calls.
//!  - `a_forwarded_slot_inside_a_built_dictionary_is_refused_too` is the third way a
//!    body reads its frame, and the one a first cut of this fix missed. It fails
//!    (loads clean, then dies at eval) if `dict_forwards_frame_slot` is dropped.
//!  - `control_the_pinned_element_still_dispatches` is the ticket's own control: pin
//!    `F` in the holder's clause and the identical driver answers Vec3(2,4,6). It
//!    passes with the change reverted, BY DESIGN — it says the fix is a refusal and
//!    not a regression of the machinery.
//!  - `control_a_callee_that_never_reads_the_slot` fails if
//!    `op_body_reads_sort_requirement_slot` is dropped from the verdict (the program is
//!    then refused although it runs). It passes with the whole change reverted.
//!  - `control_a_rule_body_goal_is_supplied_by_the_bridge` fails if the
//!    `enclosing_op` gate is dropped at the park. It passes with the whole change
//!    reverted. wi625's `layerb_bridged_op_dispatches_user_spec_via_threaded_dict` is
//!    the independent witness for the same claim; this one states the reason.

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// The holder shape the ticket measured, parameterized by the holder's `requires`
/// clause and the body of the operation the driver calls. `V` is pinned by the
/// argument at every call below; whether `F` is pinned is what each fixture varies.
fn holder_program(ns: &str, requires: &str, twice_body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.geometry.{{Vec3}}
  import anthill.prelude.{{Float}}
  import anthill.prelude.algebra.{{VectorSpace}}

  sort HolderVS
    sort V = ?
    sort F = ?
    {requires}
    operation twice(a: V) -> V = {twice_body}
  end

  sort Driver
    operation drive(a: Vec3) -> Vec3 = HolderVS.twice(a)
  end
end
"#
    )
}

/// A `Vec3(x:, y:, z:)` value. Field symbols are interned, not resolved: `Entity.named`
/// keys on the label and the declared order is (x, y, z).
fn vec3(kb: &mut KnowledgeBase, x: f64, y: f64, z: f64) -> Value {
    let functor = kb
        .try_resolve_symbol("anthill.geometry.Vec3")
        .expect("Vec3 sort");
    let named: Vec<(Symbol, Value)> = vec![
        (kb.intern("x"), Value::Float(x)),
        (kb.intern("y"), Value::Float(y)),
        (kb.intern("z"), Value::Float(z)),
    ];
    Value::Entity {
        functor,
        pos: vec![].into(),
        named: named.into(),
    }
}

/// The (x, y, z) of a Vec3 value, by field label.
fn components(kb: &KnowledgeBase, v: &Value) -> (f64, f64, f64) {
    let Value::Entity { named, .. } = v else {
        panic!("expected a Vec3 entity, got {v:?}");
    };
    let read = |label: &str| -> f64 {
        named
            .iter()
            .find(|(sym, _)| kb.local_name_of(*sym) == label)
            .map(|(_, val)| match val {
                Value::Float(f) => *f,
                other => panic!("field `{label}` is not a Float: {other:?}"),
            })
            .unwrap_or_else(|| panic!("no field `{label}` on {v:?}"))
    };
    (read("x"), read("y"), read("z"))
}

/// `<ns>.Driver.drive(Vec3(1,2,3))` must answer `want`. A FRESH interpreter per call —
/// a trapped call poisons a shared one.
fn drive_123(src: &str, ns: &str, want: (f64, f64, f64), why: &str) {
    let mut interp = crate::common::interp_for(src);
    let a = vec3(interp.kb_mut(), 1.0, 2.0, 3.0);
    let entry = format!("{ns}.Driver.drive");
    let out = interp
        .call(&entry, &[a])
        .unwrap_or_else(|e| panic!("{entry}: {why}; got {e}"));
    assert_eq!(components(interp.kb(), &out), want, "{entry}: {why}");
}

/// THE SUBJECT. `HolderVS requires VectorSpace[V, F]`; the driver's `Vec3` argument
/// pins `V` and nothing pins `F`; `twice`'s body reads the slot. Pre-fix this loaded
/// clean and raised `Internal(DeferToRequirement: … `__req_vectorspace` not bound …)`
/// at eval.
#[test]
fn sort_level_unconstrained_element_is_refused_at_load() {
    let src = holder_program(
        "test.wi945.subject",
        "requires VectorSpace[V, F]",
        "VectorSpace.vec_add(a, a)",
    );
    let errs = crate::common::try_load_kb_with(&src)
        .err()
        .unwrap_or_else(|| panic!("expected a load refusal, but the source loaded clean"));
    let refusal = errs
        .iter()
        .find(|e| e.contains("cannot be supplied"))
        .unwrap_or_else(|| panic!("no refusal among load errors:\n{}", errs.join("\n")));
    // Every piece §5.2 requires the diagnostic to name, plus the location.
    for piece in [
        // the requirement, rendered at the call's own bindings
        "anthill.prelude.algebra.VectorSpace[V = anthill.geometry.Vec3",
        // the unconstrained element — the whole point, and the word the op-level
        // twin uses for the same condition
        "F = test.wi945.subject.HolderVS.F",
        "unconstrained",
        // the construction outcome
        "no impl provides",
        // and which call it is about
        "test.wi945.subject.HolderVS.twice",
    ] {
        assert!(
            refusal.contains(piece),
            "refusal must name `{piece}`; got:\n{refusal}"
        );
    }
    assert!(
        refusal.chars().next().is_some_and(|c| c.is_ascii_digit()),
        "refusal must be located (line:col prefix); got:\n{refusal}"
    );
}

/// THE SUBJECT ONE HOP AWAY, and the reason the verdict follows same-sort calls. The
/// called operation's own body reads nothing; it delegates to a SIBLING that does.
/// A same-sort call INHERITS the caller's frame rather than building one
/// (`start_apply_same_sort`'s `inherit` arm), so the sibling reads the same empty
/// channel and the program dies at eval in exactly the subject's way — one edit to the
/// fixture away from the shape the ticket reported.
///
/// MEASURED before the transitive walk existed: this loaded CLEAN and raised
/// `Internal(DeferToRequirement: … `__req_vectorspace` not bound … running
/// `…HolderVS.inner`)`. It is the test that fails if
/// `op_body_reads_sort_requirement_slot` stops following same-sort callees.
#[test]
fn a_sibling_that_reads_the_slot_is_refused_too() {
    let src = format!(
        r#"
namespace test.wi945.sibling
  import anthill.geometry.{{Vec3}}
  import anthill.prelude.{{Float}}
  import anthill.prelude.algebra.{{VectorSpace}}

  sort HolderVS
    sort V = ?
    sort F = ?
    requires VectorSpace[V, F]
    operation inner(a: V) -> V = VectorSpace.vec_add(a, a)
    operation twice(a: V) -> V = inner(a)
  end

  sort Driver
    operation drive(a: Vec3) -> Vec3 = HolderVS.twice(a)
  end
end
"#
    );
    let errs = crate::common::try_load_kb_with(&src)
        .err()
        .unwrap_or_else(|| panic!("expected a load refusal, but the source loaded clean"));
    assert!(
        errs.iter().any(|e| e.contains("cannot be supplied")
            && e.contains("F = test.wi945.sibling.HolderVS.F")),
        "the refusal must name the unconstrained element even when the slot is read by \
         a same-sort SIBLING of the called operation; got:\n{}",
        errs.join("\n"),
    );
}

/// THE THIRD WAY A BODY READS THE FRAME, found by /code-review against a first cut that
/// counted only two. `twice`'s body calls a CROSS-SORT `Inner.innerOp`, and the typer
/// DOES build that call a dictionary — but fills its `Doubler` slot by FORWARDING
/// `HolderVS`'s own `__req_doubler` as a `var_ref` (the WI-418 forward). So the
/// dictionary is not self-contained: it reads `twice`'s frame, which is empty because
/// `VectorSpace`'s `F` is unconstrained at the driver's call.
///
/// MEASURED against the two-way cut: LOADED CLEAN, then
/// `internal evaluator error: var_ref(__req_doubler) unbound in requirement position
/// (running `…HolderVS.twice`; frame binds [])`. "Got a dictionary" is not "needs
/// nothing from me", and this is the test that says so.
#[test]
fn a_forwarded_slot_inside_a_built_dictionary_is_refused_too() {
    let src = r#"
namespace test.wi945.forward
  import anthill.geometry.{Vec3}
  import anthill.prelude.{Float}
  import anthill.prelude.algebra.{VectorSpace}

  sort Doubler
    sort V = ?
    operation dbl(a: V) -> V
  end

  sort Inner
    sort V = ?
    requires Doubler[V]
    operation innerOp(a: V) -> V = Doubler.dbl(a)
  end

  sort HolderVS
    sort V = ?
    sort F = ?
    requires VectorSpace[V, F]
    requires Doubler[V]
    operation twice(a: V) -> V = Inner.innerOp(a)
  end

  sort Driver
    operation drive(a: Vec3) -> Vec3 = HolderVS.twice(a)
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected a load refusal, but the source loaded clean"));
    assert!(
        errs.iter().any(|e| e.contains("cannot be supplied")
            && e.contains("F = test.wi945.forward.HolderVS.F")),
        "the refusal must name the unconstrained element when the callee's frame is read \
         by a `var_ref` FORWARD inside a dictionary the typer did build; got:\n{}",
        errs.join("\n"),
    );
}

/// CONTROL — the ticket's own: pin `F` in the holder's clause and the identical driver
/// runs. Says the machinery was sound and what was missing was only the refusal.
/// Passes with the change reverted, by design.
#[test]
fn control_the_pinned_element_still_dispatches() {
    let src = holder_program(
        "test.wi945.pinned",
        "requires VectorSpace[V = V, F = Float]",
        "VectorSpace.vec_add(a, a)",
    );
    drive_123(
        &src,
        "test.wi945.pinned",
        (2.0, 4.0, 6.0),
        "a concretely-pinned requirement element must still construct its dictionary",
    );
}

/// CONTROL — the unpinned element, and a callee that never reads the slot. `twice`
/// returns its argument, so entering it with no requirements channel costs nothing and
/// the program runs. THE GATE: this is the class `test.wi508g.useNew` is in
/// (`FiniteCollection.size` at an unpinned `Element`, answering 1), reproduced here at
/// the subject's own shape so the reason is stated where the refusal lives.
#[test]
fn control_a_callee_that_never_reads_the_slot() {
    let src = holder_program("test.wi945.unread", "requires VectorSpace[V, F]", "a");
    drive_123(
        &src,
        "test.wi945.unread",
        (1.0, 2.0, 3.0),
        "a body that reads no `__req_*` must not be refused for a dictionary it never wants",
    );
}

/// The gap3b shape: a `requires`-carrying sort whose body DOES read the slot, reached
/// from a RULE body. Nothing at the goal pins `Box.T` — `?b` is a variable — and that
/// is the ordinary case, because the SLD→eval bridge builds the real `Combiner`
/// dictionary from the concrete argument value at resolve time.
const BRIDGED_SRC: &str = r#"
namespace test.wi945.bridged
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.PartialEq.{eq}
  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end
  sort Tag
    entity tag(n: Int64)
  end
  sort TagCombiner
    provides Combiner[T = Tag]
    operation combine(x: Tag, y: Tag) -> Tag = tag(n: 99)
  end
  sort Box
    sort T = ?
    requires Combiner[T]
    entity box(content: T)
    operation combineBox(b: Box) -> T =
      match b
        case box(c) -> combine(c, c)
  end
  import test.wi945.bridged.Box.{combineBox}
  rule combines_to(?b, ?r) :- eq(combineBox(?b), ?r)
end
"#;

fn tag_entity(kb: &mut KnowledgeBase, v: i64) -> TermId {
    let f = kb
        .try_resolve_symbol("test.wi945.bridged.Tag.tag")
        .expect("Tag.tag");
    let n = kb.intern("n");
    let nv = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(v)));
    kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(n, nv)]),
    })
}

fn box_of(kb: &mut KnowledgeBase, content: TermId) -> TermId {
    let f = kb
        .try_resolve_symbol("test.wi945.bridged.Box.box")
        .expect("Box.box");
    let c = kb.intern("content");
    kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(c, content)]),
    })
}

/// CONTROL — the rule-body gate, DRIVEN to both verdicts so a goal that resolved
/// somewhere wrong could not pass by answering "one solution". Fails if the park's
/// `enclosing_op` gate is dropped: the program is then refused at load and neither
/// assertion is reached.
#[test]
fn control_a_rule_body_goal_is_supplied_by_the_bridge() {
    let mut kb = crate::common::load_kb_with(BRIDGED_SRC);
    let pred = kb
        .try_resolve_symbol("test.wi945.bridged.combines_to")
        .expect("combines_to");
    let mut definite = |content: i64, want: i64| -> usize {
        let t = tag_entity(&mut kb, content);
        let b = box_of(&mut kb, t);
        let r = tag_entity(&mut kb, want);
        let g = kb.alloc(Term::Fn {
            functor: pred,
            pos_args: SmallVec::from_slice(&[b, r]),
            named_args: SmallVec::new(),
        });
        kb.resolve(&[g], &ResolveConfig::default())
            .iter()
            .filter(|s| s.residual.is_empty())
            .count()
    };
    assert_eq!(
        definite(5, 99),
        1,
        "combineBox(box(tag(5))) = tag(99) via the dictionary the BRIDGE builds — the \
         goal pins nothing, and that is not a load error",
    );
    assert_eq!(
        definite(5, 5),
        0,
        "…and the same goal must FAIL at tag(5), so the solution above is the answer \
         and not merely a search that succeeded",
    );
}
