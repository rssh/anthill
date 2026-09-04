//! WI-20260828-5NSZY — an arrow pinned ONE LEVEL OUT must reach a bare operation name
//! nested inside a constructor argument.
//!
//! THE GAP. WI-20260828-2TMB5 made a bare non-nullary operation name need an arrow to lift
//! AGAINST, because a lift with nothing to pin against cannot be MINTED:
//! `attach_eta_dispatch_dict` reads the expected arrow for BOTH the requirement dictionary
//! and the argument-spread labels. That was right, and it refused a program whose author HAD
//! written the arrow — one level out. `apply_it(o: Option[T = Function[A = Int64, B =
//! Int64]], …)` fed `apply_it(some(inc), 41)` says exactly what `inc` must be; the arrow
//! simply never travelled from the parameter, through `some`, to `inc`.
//!
//! IT TAKES BOTH HALVES, and each was measured alone and found insufficient — the ticket
//! records the first as already refuted before this file existed:
//!
//!   * `arrow_field_expected_from_ctor` walks the field's declared type through the
//!     CONSTRUCTOR's own `expected` (`some`'s `value: T` becomes `Function[…]` once `T` is
//!     pinned). Alone it fires NOWHERE, because the constructor had no `expected` to walk.
//!   * `ctor_arg_unlocks_an_arrow_for_a_bare_name` supplies that `expected`, pushing the
//!     call's declared parameter type into a constructor-application argument. Alone it
//!     changes nothing, because the hint it enables is the one above.
//!
//! CONTAINMENT WAS THE RISK, and it is the gate rather than the mechanism. Pushing an
//! expected type into a constructor is not neutral: `check_constructor_iter` reads it for
//! the §8.2 classification (`expected_names_an_entity`, WI-20260826-JSFHG) and seeds it into
//! the build. So the push is gated on the walk it enables actually reaching a CALLABLE for a
//! field whose argument IS a bare operation name, AND on that field's declared type not
//! being callable already — the already-callable ones are `arrow_slot_arg_hint`'s
//! (WI-20260828-8Q0Q5), which needs no `expected`. CENSUSED with a probe on both halves over
//! the whole workspace: without the second condition the push fires on four stdlib sites
//! (`Stream.splitFirst`, `Iterable.iterator`, `FiniteCollection.collect`) and `wi8q0q5`'s
//! arrow-field carrier, every one an already-arrow field; with it, on nothing outside the
//! rows below. No stdlib call site receives a hint it did not receive before.
//!
//! TWO ROUTES THIS DOES NOT REACH, found by review and recorded rather than papered over,
//! because each is governed by something outside this ticket.
//!
//!   * A LIST/SET LITERAL. `head_apply([inc], 41)` is refused where its desugared twin
//!     `head_apply(cons(inc, nil()), 41)` returns 42. The hint is not simply missing here —
//!     it is WITHHELD, and `arg_is_tuple_literal`'s doc says why with its own measurement:
//!     `TypeBuildFrame::ListLit` takes `element_hint` as the element type UNCONDITIONALLY
//!     and never consults what the elements typed as, so a hint pushed into a list literal
//!     OVERWRITES rather than checks (`operation mk() -> List[T = Int64] = ["x"]` loads
//!     clean today). Supplying one here would trade a correct refusal for a silent accept.
//!     That hole is WI-20260826-7JDWY, still open; the literal spelling can be threaded the
//!     moment it closes, and not before.
//!
//!   * A CALLEE TYPE PARAMETER inside the arrow. With `take[X](o: Option[T = Function[A = X,
//!     B = Int64]], w: X)`, the labels go unpinned and the callback spreads by SOURCE ORDER
//!     — measured, `(acc: 3, x: 10)` gives -7. This is PRE-EXISTING and not about the
//!     nesting: the direct arrow-slot twin `take[X](f: Function[A = X, B = Int64], w: X)`
//!     answers -7 too, so the arrow arriving is not what is missing. `A = X` is simply not
//!     pinned by the time `function_slot_spread_labels` reads it. The rows below therefore
//!     use GROUND arrows where they assert a label ordering, and
//!     [`the_entity_chain_spelling_threads_too`] — whose callee does carry an `X` — asserts
//!     only that the arrow ARRIVES, which is what that shape can honestly witness.
//!
//! WHAT STAYS REFUSED, and it is the whole of WI-20260828-2TMB5: a slot that pins no arrow
//! anywhere — an `Int64` field, an `Int64` parameter — still refuses a bare operation name,
//! and a body-less operation still has no function-value form. Those rows live in
//! `wi_2tmb5_bare_op_name_zero_arg_reading_test` and are green throughout. This ticket
//! delivers the arrow where one was written; it does not weaken the rule where none was.

use crate::common::{interp_for, try_load_kb_with};

/// Evaluate `op` in `src` and return its `Int`. Loading is checked first so a load error
/// reports as itself rather than as a missing operation.
fn eval_int(src: &str, op: &str) -> i64 {
    if let Err(e) = try_load_kb_with(src) {
        panic!("must load: {e:?}");
    }
    match interp_for(src)
        .call(op, &[])
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
    {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// THE HEADLINE, DRIVEN. The ticket's own program: the arrow is pinned on `apply_it`'s
/// parameter, `inc` is nested inside `some(…)`, and the call must return 42.
///
/// DRIVEN rather than load-asserted deliberately. A clean load would be satisfied by a fix
/// that typed `inc` as the arrow and then minted something eval cannot apply — which is
/// exactly the failure mode WI-20260828-2TMB5's first cut had. Calling it is what proves the
/// `OpRef` is real.
///
/// BACKED OUT (either half): FAILS at LOAD, `type mismatch in inc.function-value
/// (op-as-fn-value)` — the arrow does not reach the name and WI-20260828-2TMB5 refuses it.
#[test]
fn an_arrow_pinned_one_level_out_reaches_the_nested_name() {
    let src = r#"
namespace wi5nszy.headline
  import anthill.prelude.{Option, Int64, Function, some, none}
  import anthill.prelude.Option.{none, some}
  operation inc(x: Int64) -> Int64 = x + 1
  operation apply_it(o: Option[T = Function[A = Int64, B = Int64]], v: Int64) -> Int64 =
    match o
      case none() -> 0
      case some(f) -> f(v)
  operation drive() -> Int64 = apply_it(some(inc), 41)
end
"#;
    assert_eq!(
        eval_int(src, "wi5nszy.headline.drive"),
        42,
        "the arrow written on the parameter must reach the bare name inside `some(…)`",
    );
}

/// THE SPREAD LABELS, which are half of what the arrow is FOR. `attach_eta_dispatch_dict`
/// reads the expected arrow to decide whether a multi-parameter callback is applied BY NAME
/// or by source order, so an arrow that arrives too late is not merely a worse message.
///
/// The tuple is written `(acc: 3, x: 10)` — the OTHER order from `sub2(x, acc)` — so source
/// order gives 3 - 10 and label order gives 10 - 3. Only the second is 7.
///
/// BACKED OUT (either half): FAILS at LOAD, naming `sub2`. Under the ABANDONED first cut of
/// WI-20260828-2TMB5 (which lifted against the operation's own arrow rather than refusing):
/// loads clean and returns **-7**, which is the measurement that rejected that approach.
#[test]
fn a_multi_parameter_callback_spreads_by_label_through_the_nesting() {
    let src = r#"
namespace wi5nszy.labels
  import anthill.prelude.{Option, Int64, Function, some, none}
  import anthill.prelude.Option.{none, some}
  operation sub2(x: Int64, acc: Int64) -> Int64 = x - acc
  operation via_option(o: Option[T = Function[A = (x: Int64, acc: Int64), B = Int64]])
      -> Int64 =
    match o
      case none() -> 0
      case some(g) -> g((acc: 3, x: 10))
  operation drive() -> Int64 = via_option(some(sub2))
end
"#;
    assert_eq!(
        eval_int(src, "wi5nszy.labels.drive"),
        7,
        "the nested callback must spread BY LABEL; -7 means the labels went unpinned and \
         eval used source order",
    );
}

/// THE DISPATCH DICTIONARY, the other half of what the arrow is for. A `requires`-carrying
/// operation eta'd through the nesting must have its dictionary built at the MINT — an
/// `OpRef` escapes to a foreign apply frame, so a dict missing at mint is missing for good
/// (WI-420). Driven end to end: `PartialEq[Int64]` has to be resolved and installed for
/// `eq(1, 1)` to answer at all.
///
/// BACKED OUT (either half): FAILS at LOAD, naming `same`.
#[test]
fn a_requires_carrying_operation_mints_its_dictionary_through_the_nesting() {
    let src = r#"
namespace wi5nszy.dict
  import anthill.prelude.{Option, Int64, Bool, Function, PartialEq, some, none}
  import anthill.prelude.Option.{none, some}
  operation same[T](a: T, b: T) -> Bool requires PartialEq[T] = PartialEq.eq(a, b)
  operation via(o: Option[T = Function[A = (Int64, Int64), B = Bool]], w: Int64) -> Int64 =
    match o
      case none() -> 0
      case some(f) -> if f((w, w)) then 1 else 0
  operation drive() -> Int64 = via(some(same), 1)
end
"#;
    assert_eq!(
        eval_int(src, "wi5nszy.dict.drive"),
        1,
        "a `requires`-carrying operation eta'd through the nesting must carry its \
         dispatch dictionary from the mint",
    );
}

/// THE ENTITY-CHAIN SPELLING. `Option` reaches its element directly; `List` reaches it
/// through `cons`'s `head: T` — a different constructor, a different field, and the shape
/// `wi836_type_var_arg_agreement_test` is built on. Both must thread, and a fix that walked
/// only the direct case would leave this one refused.
///
/// WHAT THIS ROW CANNOT WITNESS, and the reason it is not written as a spread assertion:
/// `take`'s arrow carries the callee type parameter `X`, and with an `X` in the arrow the
/// labels go unpinned and the callback spreads by source order — PRE-EXISTING, since the
/// direct arrow-slot twin answers the same. So this row asserts that the arrow ARRIVES (the
/// program loads and runs), and the label ordering is asserted where it can be measured, on
/// the ground arrow of [`a_multi_parameter_callback_spreads_by_label_through_the_nesting`].
/// `take`'s body is `= 1` for the same reason — applying the callback here would measure the
/// pre-existing gap, not this ticket.
///
/// BACKED OUT (either half): FAILS at LOAD, naming `sub2`.
#[test]
fn the_entity_chain_spelling_threads_too() {
    let src = r#"
namespace wi5nszy.chain
  import anthill.prelude.{List, Int64, Function}
  import anthill.prelude.List.{nil, cons}
  operation sub2(a: Int64, b: Int64) -> Int64 = a - b
  operation take[X](l: List[T = Function[A = X, B = Int64]], w: X) -> Int64 = 1
  operation go() -> Int64 = take(cons(sub2, nil()), (3, 10))
end
"#;
    assert_eq!(eval_int(src, "wi5nszy.chain.go"), 1);
}

/// THE EPONYMOUS PARAMETRIC SPELLING — `sort Wrap { sort T = ?; entity Wrap(v: T) }`,
/// where the constructor and its sort are ONE symbol. Found by review, and it was refused
/// while the `Option`/`some` spelling of the identical program returned 42 and a lambda in
/// the same slot returned 41 — one author-written arrow, three verdicts by spelling.
///
/// The cause was `ctor_field_expected` reading `strict_parent_sort`, which subtracts exactly
/// the reflexive case. WI-946 had left that one strict reader in place and written down why:
/// "no probe made the difference observable … converting is still the right move the moment
/// one exists." WI-20260828-2TMB5 created it, by making a missing hint a REFUSAL rather than
/// a worse inference. This row is that probe.
///
/// BACKED OUT (`sort_of_constructor` → `strict_parent_sort`): FAILS at LOAD, naming `inc`.
#[test]
fn the_eponymous_parametric_spelling_threads_too() {
    let src = r#"
namespace wi5nszy.eponymous
  import anthill.prelude.{Int64, Function}
  sort Wrap
    import anthill.prelude.{Int64, Function}
    sort T = ?
    entity Wrap(v: T)
  end
  operation inc(x: Int64) -> Int64 = x + 1
  operation apply_it(w: Wrap[T = Function[A = Int64, B = Int64]], v: Int64) -> Int64 =
    match w
      case Wrap(f) -> f(v)
  operation drive() -> Int64 = apply_it(Wrap(inc), 41)
end
"#;
    assert_eq!(eval_int(src, "wi5nszy.eponymous.drive"), 42);
}

/// A CONSTRUCTOR NESTED IN A CONSTRUCTOR FIELD, rather than in an operation-call argument.
/// Found by review. The first cut wired the supplier
/// (`ctor_arg_unlocks_an_arrow_for_a_bare_name`) into `one_arg_hint` only, so the
/// constructor-field chains got the READER (`arrow_field_expected_from_ctor`) with nothing
/// to supply their `expected` — and `run(holder(some(inc)), 41)` was refused while
/// `apply_it(some(inc), 41)`, on the very same `Option[T = Function[…]]` slot, returned 42.
///
/// A hint that reaches an argument down one route and not another is the defect class this
/// ticket exists to close, so the two routes get the same supplier rather than a second one.
///
/// BACKED OUT (drop the supplier from the two constructor-field chains, keeping it in
/// `one_arg_hint`): FAILS at LOAD, naming `inc`.
#[test]
fn a_constructor_nested_in_a_constructor_field_threads_too() {
    let src = r#"
namespace wi5nszy.ctorfield
  import anthill.prelude.{Option, Int64, Function, some, none}
  import anthill.prelude.Option.{none, some}
  sort Holder
    import anthill.prelude.{Option, Int64, Function}
    entity holder(o: Option[T = Function[A = Int64, B = Int64]])
  end
  operation inc(x: Int64) -> Int64 = x + 1
  operation run(h: Holder, v: Int64) -> Int64 =
    match h
      case holder(o) ->
        match o
          case none() -> 0
          case some(f) -> f(v)
  operation drive() -> Int64 = run(holder(some(inc)), 41)
end
"#;
    assert_eq!(eval_int(src, "wi5nszy.ctorfield.drive"), 42);
}

/// CONTROL — a slot that pins NO arrow anywhere still refuses the bare name, which is
/// WI-20260828-2TMB5's rule and the thing this ticket must not weaken. Passes either way BY
/// DESIGN: the walk reaches `Int64`, which is not callable, so neither half fires. Without
/// this row every row above is satisfied by a fix that simply pushes every parameter type
/// into every constructor argument and lets the bare name lift against whatever it finds.
#[test]
fn a_slot_that_pins_no_arrow_still_refuses() {
    let src = r#"
namespace wi5nszy.noarrow
  import anthill.prelude.{Option, Int64, some, none}
  import anthill.prelude.Option.{none, some}
  operation inc(x: Int64) -> Int64 = x + 1
  operation apply_it(o: Option[T = Int64]) -> Int64 =
    match o
      case none() -> 0
      case some(v) -> v
  operation drive() -> Int64 = apply_it(some(inc))
end
"#;
    let errs = try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("inc") && e.contains("op-as-fn-value")),
        "an `Option[T = Int64]` element pins no arrow, so the bare name must stay refused; \
         got: {errs:?}",
    );
}

/// CONTROL — the INLINE LAMBDA twin of the headline, in the same nested slot. Passes either
/// way BY DESIGN: a lambda is typed from its own text, so it never needed the arrow to
/// arrive. It is what makes the rows above experiments about the BARE-NAME reading rather
/// than about nested callback slots in general.
///
/// THE BODY IS `x`, NOT `x + 1`, AND THAT IS ITSELF A MEASUREMENT. The hint this ticket
/// delivers is gated on the argument being a bare OPERATION NAME, so a lambda in the very
/// same nested slot still receives NO expected type — `lambda x -> x + 1` there is refused
/// `ambiguous dispatch of Additive.add`, its binder pinned by nothing. That is PRE-EXISTING
/// and unchanged by this ticket (measured both ways), and it is the honest boundary of what
/// was delivered: the arrow now reaches a nested bare NAME, and does not yet reach a nested
/// lambda BINDER. Widening the gate to every callback-shaped argument is a bigger change —
/// it would push an expected type into constructors for a far larger population than the
/// census here covers. An identity lambda needs no binder type and so isolates the reading
/// this row is actually about.
#[test]
fn the_inline_lambda_twin_needed_none_of_this() {
    let src = r#"
namespace wi5nszy.lambda
  import anthill.prelude.{Option, Int64, Function, some, none}
  import anthill.prelude.Option.{none, some}
  operation apply_it(o: Option[T = Function[A = Int64, B = Int64]], v: Int64) -> Int64 =
    match o
      case none() -> 0
      case some(f) -> f(v)
  operation drive() -> Int64 = apply_it(some(lambda x -> x), 41)
end
"#;
    assert_eq!(eval_int(src, "wi5nszy.lambda.drive"), 41);
}
