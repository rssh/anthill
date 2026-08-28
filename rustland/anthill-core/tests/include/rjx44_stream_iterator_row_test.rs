//! WI-20260828-RJX44 — `Stream.iterator`'s return was a BARE `Stream`, so the stream it
//! hands back carried no element and no effect row, and a consumer that pays the row
//! (`takeN`, whose `effects s.E` reads the receiver) had nothing to read.
//!
//! ```anthill
//! operation iterator(s: Stream) -> Stream = s                      -- element and row UNWRITTEN
//! operation iterator(s: Stream) -> Stream[T = s.T, E = s.E] = s    -- what it says now
//! ```
//!
//! Every sibling on the sort already wrote the projections — `tail(s) -> Stream[T = s.T,
//! E = s.E]`, `splitFirst`'s `B` likewise — so this was the one signature that dropped them.
//! The identity body `= s` makes the projected form exactly as true as the bare one; it just
//! says more.
//!
//! WHY IT LOOKED LIKE A DISPATCH BUG, recorded because two earlier framings of this ticket
//! were wrong and cost real time. `Iterable.iterator(c: C) -> Stream[Element, E]` names the
//! SPEC's own params and grounds by ordinary carrier-param binding, so the two spellings of
//! "give me the iterator" behaved differently and that difference read first as
//! dot-vs-qualified and then as something about carriers with computed rows. It is neither:
//! the qualified `Stream.iterator(xs)` on a plain `List` fails on main, and it fails because
//! of what its own signature omits.
//!
//! CONTROLS: `control_iterable_iterator_*` uses the spec-param spelling and `control_ascribed`
//! pins the row from the call site; both pass with the change backed out (revert the
//! signature to a bare `-> Stream`), while the two driving cases fail with
//! `undeclared effect: ?_`.

fn expect_loads(name: &str, body: &str) {
    let src = format!(
        "\nnamespace rjx44\n  import anthill.prelude.{{Int64, List, Stream, Iterable}}\n  import anthill.prelude.List.{{length}}\n  import anthill.prelude.Stream.{{takeN}}\n{body}\nend\n"
    );
    if let Err(errs) = crate::common::try_load_kb_with(&src) {
        panic!("{name} must load clean; got {} error(s):\n{}", errs.len(), errs.join("\n"));
    }
}

/// DRIVES THE FIX — the result flows into `takeN`, which pays the receiver's row, so nothing
/// at the use site pins it. RED with the signature reverted.
#[test]
fn stream_iterator_result_carries_its_row() {
    expect_loads(
        "qualified Stream.iterator into takeN",
        "  operation a(xs: List[T = Int64]) -> Int64 =\n    length(takeN(Stream.iterator(xs), 1000))",
    );
}

/// DRIVES THE FIX — the dot spelling, which resolves to that same op, and is how real code
/// reaches it. RED with the signature reverted.
#[test]
fn dot_iterator_result_carries_its_row() {
    expect_loads(
        "xs.iterator() into takeN",
        "  operation b(xs: List[T = Int64]) -> Int64 =\n    length(takeN(xs.iterator(), 1000))",
    );
}

/// CONTROL — `Iterable.iterator` writes the row through the SPEC's own params, so it never
/// depended on the projections. Green either way.
#[test]
fn control_iterable_iterator_grounds_by_carrier_param() {
    expect_loads(
        "Iterable.iterator into takeN",
        "  operation c(xs: List[T = Int64]) -> Int64 =\n    length(takeN(Iterable.iterator(xs), 1000))",
    );
}

/// CONTROL — an ascribing return pins the row at the call site, so the omission never
/// surfaced there. Green either way; it is why the gap survived.
#[test]
fn control_ascribed_call_site_pins_the_row() {
    expect_loads(
        "ascribed Stream.iterator",
        "  operation d(xs: List[T = Int64]) -> Stream[T = Int64, E = {}] =\n    Stream.iterator(xs)",
    );
}
