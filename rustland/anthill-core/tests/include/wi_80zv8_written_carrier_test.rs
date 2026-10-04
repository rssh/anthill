//! WI-20261001-80ZV8, stage (c), part 1 — A PROVISION'S CARRIER WRITTEN WITH ITS SLOTS
//! ANSWERS AS THE BARE NAME DOES.
//!
//! `sort Stream … provides Iterable[C = Stream, Element = T, E = E]` says every carrier of
//! `Stream` is iterable. The bare `Stream` there is what proposal 070 retires inside a sort's
//! own definition; its replacement is `Self`, which lowers to `Stream[T = T, E = E]` — and
//! that form, legal all along, did not work: written that way the stdlib had eleven load
//! errors from the one line (MEASURED, the hand-written form and `Self` alike), because
//! three readers treated the two spellings differently. Each is a part below.
//!
//! The fixtures are miniatures of the stdlib's own shapes — `Iter` for `Iterable`, `Strm`
//! for `Stream`, `Drop` for `FilteredStream` — so the rows hold whatever the stdlib writes.
//! Every row that can RUNS and names its value.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED (2026-10-03), each part present but disabled, over this file's 9 rows.
//!
//! IN THE TREE AS IT IS — the stdlib's `Stream` writes its own provision `C = Self` — every
//! part's back-out stops THE STDLIB loading, so every row of the suite fails, these nine
//! among them: part 1, eleven errors (six `no impl matches`, five `provides …, which requires
//! …, but … does not provide …`); part 2 or part 3, one — `FilteredStream.splitFirst`'s
//! `Stream.splitFirst.dispatch`. The figures below say which rows of THIS file each part
//! carries, measured with that one stdlib line written bare so that the stdlib loads:
//!
//! 1. THE RESOLVER READS A CARRIER AT THE SORT IT PROVIDES (typing/candidates.rs,
//!    `match_candidate_against_goal` arm (2a) and `carrier_viewed_at`). 6 FAIL:
//!    [`a_written_carrier_binding_answers_for_each_carrier`],
//!    [`self_in_a_specs_own_provision_is_the_written_form`],
//!    [`a_written_carrier_binding_answers_for_a_parameterless_carrier`],
//!    [`a_written_carrier_binding_answers_through_a_chain_of_provisions`],
//!    [`a_witnesss_written_carrier_answers_for_a_carrier_of_that_spec`] and
//!    [`a_wrapper_over_a_rewrapped_tail_runs_with_a_written_provision`] — refused `no impl
//!    matches` and `provides …, which requires …, but … does not provide …`.
//!    1a. …AND A PARAMETERLESS CARRIER IS A SORT APPLIED TO NOTHING (`carrier_viewed_at`'s
//!    bare-sort arm; the stdlib loads either way). 3 FAIL: the parameterless row, the chain
//!    row and the written wrapper row — `Deep` and `Range` have no parameter either.
//! 2. AN ARGUMENT TYPED BY AN ABSTRACT SPEC FILLS THE CARRIER SLOT WITH ITS WHOLE TYPE
//!    (typing/constructor.rs `bare_spec_arg_provision_projection`). 3 FAIL: both wrapper
//!    rows and [`the_carrier_slot_takes_the_arguments_whole_type`] (`Source = ??_`). The
//!    BARE wrapper row fails too, and differently — `expected Option[T = Pair[A = ?T, …]],
//!    got Option[T = Pair[A = ?A, …]]`: nothing threads the wrapper's element from the tail.
//!    The stdlib's `FilteredStream` loaded without this part only because a SIBLING field,
//!    its predicate, pins the element; `Drop` has no such field.
//! 3. A ROW VARIABLE IS THREADED AS ITSELF (typing/constructor.rs `effect_row_param_value`).
//!    NOT SEPARABLE FROM PART 2: with the carrier named and the row still wrapped, the goal
//!    carries `E = {ES}` beside a carrier whose row is `ES`, and the stdlib's
//!    `FilteredStream.splitFirst` is refused under EITHER spelling of the provision — so all
//!    nine fail with the suite. The row that names the difference is
//!    [`the_carrier_slot_takes_the_arguments_whole_type`] (`ES = {?ES}`).
//!
//! Every row fails under at least one part but
//! [`a_bare_carrier_binding_answers_for_each_carrier`], the control: the bare spelling of the
//! first row, which ran before and runs now — it is what the written rows are now equal to.

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

// ── The carrier binding of a spec's own provision ───────────────────────────

/// `Strm` provides `Iter` with its carrier written `carrier`; `carrier_sort` provides
/// `Strm` and `Fin`, and `Fin` requires `Iter` — so a call through `Iter`'s bodied member
/// and the load-time check of `Fin`'s requirement both ask for `Iter` at the carrier.
fn provision_program(ns: &str, carrier: &str, carrier_sort: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}

  sort Iter
    sort C = ?
    sort Element = ?
    effects E = ?
    operation first(c: C) -> Element effects E
    operation firstTwice(c: C) -> Element effects E = first(c)
  end

  sort Fin
    sort C = ?
    sort Element = ?
    effects E = ?
    requires Iter[C = C, Element = Element, E = E]
    operation count(c: C) -> Int64
  end

  sort Strm
    sort T = ?
    effects E = ?
    operation head(s: Strm) -> s.T effects s.E
    provides Iter[C = {carrier}, Element = T, E = E]
    operation first(s: Strm) -> s.T effects s.E = head(s)
  end

{carrier_sort}
end
"#
    )
}

/// A carrier with a parameter: `One[T]`.
const PARAMETRIC_CARRIER: &str = r#"
  sort One
    sort T = ?
    entity one(v: T)
    provides Strm[T, {}]
    operation head(o: One) -> T = o.v
    provides Fin[C = One[T], Element = T, E = {}]
    operation count(o: One) -> Int64 = 1
  end

  operation go() -> Int64 = Iter.firstTwice(one(v: 7)) + Fin.count(one(v: 1))
"#;

/// A carrier with none: `Uno`.
const PARAMETERLESS_CARRIER: &str = r#"
  sort Uno
    entity uno(v: Int64)
    provides Strm[T = Int64, E = {}]
    operation head(u: Uno) -> Int64 = u.v
    provides Fin[C = Uno, Element = Int64, E = {}]
    operation count(u: Uno) -> Int64 = 2
  end

  operation go() -> Int64 = Iter.firstTwice(uno(v: 7)) + Fin.count(uno(v: 1))
"#;

/// THE WRITTEN FORM ANSWERS FOR EVERY CARRIER: `provides Iter[C = Strm[T = T, E = E], …]`
/// serves `One[T = Int64]`, which is a `Strm[T = Int64, E = {}]` by its own provision. It was
/// refused three ways (MEASURED): `Iter.firstTwice.dispatch` and `Fin.count.dispatch`, each
/// `no impl matches — unresolved: Iter[C = One[T = Int64], …]`, and `'One' provides 'Fin',
/// which requires 'Iter', but 'One' does not provide 'Iter'`.
#[test]
fn a_written_carrier_binding_answers_for_each_carrier() {
    let src = provision_program("wi80zv8c.w1", "Strm[T = T, E = E]", PARAMETRIC_CARRIER);
    assert_eq!(run_src(&src, "wi80zv8c.w1.go"), Ok(8));
}

/// `Self` IS THAT FORM, in the position proposal 070 needs it most: a spec naming itself as
/// the carrier of what it provides.
#[test]
fn self_in_a_specs_own_provision_is_the_written_form() {
    let src = provision_program("wi80zv8c.w2", "Self", PARAMETRIC_CARRIER);
    assert_eq!(run_src(&src, "wi80zv8c.w2.go"), Ok(8));
}

/// CONTROL — the bare spelling. Passes with or without this change by design: it is what the
/// two rows above are now equal to.
#[test]
fn a_bare_carrier_binding_answers_for_each_carrier() {
    let src = provision_program("wi80zv8c.w3", "Strm", PARAMETRIC_CARRIER);
    assert_eq!(run_src(&src, "wi80zv8c.w3.go"), Ok(8));
}

/// …AND FOR A CARRIER WITH NO PARAMETER: `Uno` is a `Strm[T = Int64, E = {}]` too, and a
/// sort applied to nothing is not an application — the reader of one has to be asked for it
/// separately.
#[test]
fn a_written_carrier_binding_answers_for_a_parameterless_carrier() {
    let src = provision_program("wi80zv8c.w4", "Self", PARAMETERLESS_CARRIER);
    assert_eq!(run_src(&src, "wi80zv8c.w4.go"), Ok(9));
}

/// A carrier TWO provisions from `Strm`: `Deep` provides `Mid`, a spec whose own provision
/// says every `Mid` is a `Strm`. `head` is `Deep`'s own. (A `Mid` that IMPLEMENTS `head` for
/// its carriers — `operation head(m: Mid) -> m.T = peek(m)` — loads and then dies at eval,
/// `OperationBodyMissing { name: "….Strm.head" }`, under EITHER spelling of the provision:
/// measured while writing this row, and a gap of its own.)
const TWO_HOP_CARRIER: &str = r#"
  sort Mid
    sort T = ?
    provides Strm[T = T, E = {}]
  end

  sort Deep
    entity deep(v: Int64)
    provides Mid[T = Int64]
    operation head(d: Deep) -> Int64 = d.v
    provides Fin[C = Deep, Element = Int64, E = {}]
    operation count(d: Deep) -> Int64 = 3
  end

  operation go() -> Int64 = Iter.firstTwice(deep(v: 7)) + Fin.count(deep(v: 1))
"#;

/// …AND THROUGH A CHAIN: the carrier is read at the spec through every provision between
/// them, so `Deep` — a `Mid[T = Int64]`, and through `Mid` a `Strm[T = Int64, E = {}]` —
/// is answered for as `One` is.
#[test]
fn a_written_carrier_binding_answers_through_a_chain_of_provisions() {
    for (ns, carrier) in [("wi80zv8c.w5", "Self"), ("wi80zv8c.w6", "Strm")] {
        let src = provision_program(ns, carrier, TWO_HOP_CARRIER);
        assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(10), "{carrier}");
    }
}

/// THE RULE IS NOT ABOUT `Self`: a WITNESS that provides `Iter` for streams, its carrier
/// written `Strm[T = A]`, answers for `One[T = Int64]` too — and its own parameter `A` is
/// bound from the reading (`One` is a `Strm[T = Int64]`), which is what types `go`. It was
/// refused `no impl matches`: the witness covered a value typed `Strm[…]` and nothing that
/// IS one.
#[test]
fn a_witnesss_written_carrier_answers_for_a_carrier_of_that_spec() {
    let src = r#"
namespace wi80zv8c.w7
  import anthill.prelude.{Int64}

  sort Iter
    sort C = ?
    sort Element = ?
    operation first(c: C) -> Element
    operation firstTwice(c: C) -> Element = first(c)
  end

  sort Strm
    sort T = ?
    operation head(s: Strm) -> s.T
  end

  sort One
    sort T = ?
    entity one(v: T)
    provides Strm[T = T]
    operation head(o: One) -> T = o.v
  end

  sort StrmIter
    sort A = ?
    provides Iter[C = Strm[T = A], Element = A]
    operation first(s: Strm[T = A]) -> A = Strm.head(s)
  end

  operation go() -> Int64 = Iter.firstTwice(one(v: 7))
end
"#;
    assert_eq!(run_src(src, "wi80zv8c.w7.go"), Ok(7));
}

// ── A wrapper that re-wraps its source's tail ───────────────────────────────

/// A miniature of the stdlib's lazy combinators. `Drop` wraps any `Iter` source and is a
/// `Strm` of it without its first `n` elements; its `splitFirst` takes the source's first
/// element off and RE-WRAPS THE TAIL — `drop(rest, n - 1)`, where `rest` is typed by the spec
/// `Strm` and not by a carrier — then dispatches `Strm.splitFirst` on the new wrapper, which
/// needs `Drop`'s own `requires Iter[C = Source, …]` at that tail. `tail_use` is the body of
/// the re-wrapping branch.
fn wrapper_program(ns: &str, carrier: &str, tail_use: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Option, Pair}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}

  sort Iter
    sort C = ?
    sort Element = ?
    effects E = ?
    operation iterator(c: C) -> Strm[T = Element, E = E]
  end

  sort Strm
    sort T = ?
    effects E = ?
    operation splitFirst(s: Strm) -> Option[Pair[A = s.T, B = Strm[T = s.T, E = s.E]]] effects s.E
    provides Iter[C = {carrier}, Element = T, E = E]
    operation iterator(s: Strm) -> Strm[T = s.T, E = s.E] = s
  end

  sort Range
    entity range(from: Int64, to: Int64)
    provides Strm[T = Int64, E = {{}}]
    operation splitFirst(r: Range) -> Option[Pair[A = Int64, B = Strm[T = Int64, E = {{}}]]] =
      match r
        case range(a, b) ->
          if Int64.lt(a, b) then some(pair(a, range(from: a + 1, to: b)))
          else none
  end

  sort Drop
    sort Source = ?
    sort T = ?
    effects ES = ?
    requires Iter[C = Source, Element = T, E = ES]
    entity drop(source: Iter[C = Source, Element = T, E = ES], n: Int64)
    provides Strm[T = T, E = {{ES}}]
    operation splitFirst(d: Drop) -> Option[Pair[A = T, B = Strm[T = T, E = {{ES}}]]] effects {{ES}} =
      match d
        case drop(src, n) ->
          match Strm.splitFirst(Iter.iterator(src))
            case none() -> none
            case some(pair(h, rest)) ->
              match n
                case 0 -> some(pair(h, rest))
                case _ ->
{tail_use}
  end

  operation go() -> Int64 =
    let r = range(from: 5, to: 9)
    let d = drop(r, 2)
    match Strm.splitFirst(d)
      case none() -> 0
      case some(pair(h, _)) -> h
end
"#
    )
}

/// The re-wrapping branch as the stdlib writes it.
const REWRAP: &str = "                  Strm.splitFirst(drop(rest, n - 1))";

/// A WRAPPER OVER A RE-WRAPPED TAIL RUNS WITH A WRITTEN PROVISION: dropping two of `5, 6, 7,
/// 8` leaves `7` first. The same program is the stdlib's `FilteredStream.splitFirst`, which
/// was the one error left once the resolver read a written carrier — `Stream.splitFirst
/// .dispatch … unresolved: Iterable[C = <a variable>, …]` — because nothing had told the new
/// wrapper what its `Source` is.
#[test]
fn a_wrapper_over_a_rewrapped_tail_runs_with_a_written_provision() {
    for (ns, carrier) in [
        ("wi80zv8c.d1", "Strm[T = T, E = E]"),
        ("wi80zv8c.d2", "Self"),
    ] {
        assert_eq!(
            run_src(&wrapper_program(ns, carrier, REWRAP), &format!("{ns}.go")),
            Ok(7),
            "{carrier}"
        );
    }
}

/// …AND WITH THE BARE ONE. Not a control: it passes under part 1 backed out (the bare
/// spelling never needed that step) and FAILS under part 2 — the wrapper's element is then
/// not threaded from the tail at all, which the stdlib's `FilteredStream` never showed
/// because its predicate field pins the element — and under part 3.
#[test]
fn a_wrapper_over_a_rewrapped_tail_runs_with_the_bare_provision() {
    assert_eq!(
        run_src(
            &wrapper_program("wi80zv8c.d3", "Strm", REWRAP),
            "wi80zv8c.d3.go"
        ),
        Ok(7)
    );
}

/// THE RULE IN ITS OWN TERMS (user, 2026-10-03): an argument typed by a spec fills the
/// carrier slot with ITS WHOLE TYPE — the sort at the input's own parameters — and a row
/// that is a variable arrives as that variable. A deliberately false annotation makes the
/// typer print the wrapper's type: it was `Drop[T = ?T, Source = ??_, ES = ?ES]`, the source
/// an open variable; with the carrier named and the row still wrapped it would be `ES =
/// {?ES}`, a second spelling of the same row that the resolver does not equate with `?ES`.
#[test]
fn the_carrier_slot_takes_the_arguments_whole_type() {
    let probe = "                  let probe: Int64 = drop(rest, n - 1)\n                  none";
    assert_refused_naming(
        &load_errors(&wrapper_program("wi80zv8c.d4", "Self", probe)),
        &["probe.annotation (let-binding): expected Int64, got Drop[T = ?T, Source = Strm[T = ?T, E = ?ES], ES = ?ES]"],
        "the type of `drop(rest, n - 1)`",
    );
}
