## Attributes

- id: WI-20260904-DTY3B-why-typechild-accept
- created: 2026-09-04T14:54:14Z

- status: Verified
- status_agent: user
- status_at: 2026-09-06T16:08:46Z

- acceptance: cargo-test, scaland-sbt-test

## Description

why TypeChild accept hash-consed TermId, what is the reason to have no Occurrence and not
accept Value

ANSWERED AND CLOSED 2026-09-06. The implementation is WI-20260904-02ERR, which no longer
depends on this ticket: the answer below is the whole deliverable, and leaving an edge
made 02ERR unclaimable behind a question that was already answered.

THE ANSWER, IN ONE LINE. The two carriers are a CHOICE, not a constraint, and the rule the
code applies today is the wrong one:

    the carrier is chosen by whether a subtree is WORTH SHARING,
    not by whether it is CAPABLE of being shared.

Today a subtree is interned UNLESS a `denoted` sits beneath it. A transient `?T` CAN be
interned, so it is; the `(a: ?T, b: Int64)` above it can be, so it is — and `?T` is unique
per site, so that term is shareable with nothing at all. `make_sort_ref` COULD build an
occurrence (`span` and `owner` are threaded through every lowering that reaches it), so
interning is not forced anywhere; it is simply the one thing that genuinely PAYS for a
`sort_ref` — `Int64` across 500 signatures is one `TermId` against 500 identity-bearing
`Rc`s and a deep equality. Keep it there, and only there.

WHERE THE ARM GOES — DECIDED 2026-09-06, and this is the correction to what this ticket
first sketched. Its enum block proposed a third `TypeChild` arm. That shape is REFUSED:
`typing.rs`'s row-IR argument states across four sites, one of them a live
`unreachable!("a param type is Term or Node")` (load.rs), that a type is minted as a term
OR as an occurrence and THERE IS NO THIRD. So the arm belongs on `TypeNode`:

    TypeNode::Var(VarId)   // a per-site-unique type variable — never interned

A variable then rides as `TypeChild::Node(Rc<NodeOccurrence>)` whose kind is
`TypeNode::Var`, so it IS an occurrence and the term-or-occurrence invariant survives
untouched. What this costs instead is stated at the site (node_occurrence.rs, the
`TypeNode` membership doc, which names this ticket and 02ERR): the membership rule is "a
form gets an arm iff it can TRANSITIVELY CONTAIN a `denoted`", and a variable is a LEAF.
The rule widens to "…OR needs an identity of its own". That is the honest price, and it is
one sentence.

TWO THINGS FALL OUT FREE, MEASURED 2026-09-06.
  * THE NARROWING IS ONE FUNCTION. `value_to_type_child` (typing.rs:3403) is three arms
    over ten call sites; `Value::Var(..)` currently lands on a `debug_assert!` calling it
    "a typer bug". That assert is WI-1079's half-landing seen from the building end —
    `type_head` two thousand lines away calls the same form "perfectly well-formed".
  * CONTAINERS NEED NO SPECIAL CASE. Every container lowering already asks "is any child
    NOT interned?" (load.rs:25586, `matches!(c, TypeChild::Node(_))`). A variable child
    makes its container non-interned by the SAME rule a `denoted` child does, with nobody
    writing an arm for it.

WHERE THE RISK ACTUALLY LIVES — CENSUSED 2026-09-06, and it is not in the arm. Of the
`TypeNode` match sites, 27 are exhaustive (a new arm is a COMPILE ERROR, which is what we
want) and 11 carry a `_ =>` that would swallow it SILENTLY. The sharpest is
anthill-cpp-gen/src/lib.rs:4051, which tests effect-row parameter identity by a
`Term::Var(v)` VarId compare with `_ => EffectLabel::Unreadable` beneath it: a row
variable that stops being interned degrades that path to `Unreadable` with no diagnostic.
Census the `_` arms first — a new variant's real population is the arms that do not name
it — and cpp-gen's is a REQUIRED fix, not an audit note.

SCOPE CHOSEN 2026-09-06 (user): move EVERY type variable that reaches the
TypeNode/TypeChild hierarchy, not only the two inference producers. The narrower option —
scoping to `type_check_node` rung 3 and `bind_and_label_pattern`'s `?pat` fallback — was
weighed and rejected because it leaves ONE concept with TWO carriers, which is the split
WI-20260904-5NM85 is already open about.

SEE ALSO. WI-20260904-RB0Z5 asks the same question from the value's side (answered there).
WI-20260904-02ERR carries the implementation, the producer census (there are TWO mints,
not one) and the unbounded-per-load cost measurement.

