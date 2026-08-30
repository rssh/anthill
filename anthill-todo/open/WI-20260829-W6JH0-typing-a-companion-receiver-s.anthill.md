## Attributes

- id: WI-20260829-W6JH0-typing-a-companion-receiver-s
- created: 2026-08-29T23:22:44Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T23:22:44Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPING: a companion receiver's type-arg bracket is INERT -- `Map[K = Bool, V = Bool].empty()` accepts a String key with no diagnostic.

SURFACED BY /code-review ON WI-20260829-BAD3V, which made the two-bracket spelling
`Map[K = String, V = Int64].empty[T = Int64](x)` newly writable and so put a read bracket
and a dropped one side by side. The REVIEW read the drop as introduced there; it is not,
and this ticket is the pre-existing half, filed rather than left in a test comment.

MEASURED, all three load with ZERO errors:

  operation build() -> Int64 = size(put(Map[K = String, V = Int64].empty(), "a", 1))
  operation build() -> Int64 = size(put(Map.empty(), "a", 1))
  operation build() -> Int64 = size(put(Map[K = Bool, V = Bool].empty(), "a", 1))   <-- !!

The third writes `K = Bool, V = Bool` and then puts a `String` key and an `Int64` value.
It is accepted. So the receiver's bracket is not merely dropped from the CALL -- it
constrains nothing at all, and does not even catch a direct contradiction with the
argument types it appears to annotate.

THE MECHANISM. `Map[…].empty` is a `field_access` whose object is an `application`.
`collect_field_access_segments` (parse/convert.rs) takes form (3) of proposal 035 and
flattens it to the segments `Map.empty` with, in its own words, "bindings erased" -- the
runtime call path wants the sort's NAME. Nothing downstream ever sees `K`/`V`, so the typer
infers them from the arguments and the written bindings are inert text.

WHY IT LOOKS DELIBERATE AND STILL IS NOT SETTLED. The erasure is what makes form (3) work
at all (`map_builtins_test::form_3_instantiation_receiver_parses_and_runs` drives it), and
a type-erased runtime does not need K/V. But an author writing them is making a claim, and
the language checks every other written type claim. Two coherent answers:

  (a) HONOUR THEM -- unify the receiver's bindings against the sort's params for the call,
      so the third program above is a located type error. This is the reading every other
      written binding gets.
  (b) REFUSE THEM -- if the receiver bracket cannot be honoured, a written one is a load
      error naming form (3) and telling the author to drop it or annotate the result.

Either is better than the present silence, and (b) is cheap if (a) is not wanted.

WHAT BAD3V CHANGED, so this is not re-derived: it made the CALLEE bracket readable on this
shape (`Map[…].empty[T = Int64]()` now carries type args on the same channel
`Map.empty[T = Int64]()` always did). It did not touch the receiver bracket. The two are
independent -- `Map[K = Bool].empty()` was already inert before BAD3V, which is the
measurement above.

ACCEPTANCE: `Map[K = Bool, V = Bool].empty()` with a String key is a LOCATED error (or the
bracket itself is refused, if (b) is chosen); the working form-(3) rows in
`map_builtins_test` stay green and are named as the controls that pass either way; and if
(a) is taken, say what happens when the receiver's bindings and the callee's bracket bind
the SAME name, since BAD3V's spelling now admits both at once.

