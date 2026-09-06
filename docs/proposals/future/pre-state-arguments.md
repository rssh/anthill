# Future: Pre-state arguments in operation contracts

**Status:** Draft for discussion, 2026-09-05. Unnumbered future proposal;
not implemented or committed to the roadmap. See [README](README.md).

## Proposal

`old` denotes the operation's **pre-state arguments**. `old.b` selects the
argument named `b` as observed at operation entry. It is an implicit contract
namespace, not a function to which an arbitrary expression is passed.

`arguments` explicitly names the ordinary argument namespace. Thus
`arguments.b` and the existing bare `b` identify the same argument; observations
through them use the state of the clause being evaluated. In `requires` that
is entry state; in `ensures` it is the state on normal return.

The intended vocabulary is:

| Expression | Meaning in `ensures` |
|---|---|
| `b`, `arguments.b` | Argument `b`, observed in the return state |
| `old.b` | Argument `b`, observed in the entry state |
| `result` | The operation's return value |

Argument bindings do not need to change for this distinction to matter.
An immutable argument can contain a handle to mutable state.

## Motivation: a bounded FIFO buffer

A buffer has a fixed capacity and a mutable cell containing an immutable list.
Its `contents(b)` observer reads that cell. Without pre-state arguments, a
contract can expose a `before` list as an extra ordinary parameter:

```anthill
operation push(b: BoundedBuffer, x: b.T, before: List[b.T]) -> Unit
  requires (contents(b) = before), size(b) < capacity(b)
  ensures (contents(b) = append(before, cons(x, nil())))
  effects Modify[b.state]
```

The extra parameter serves the specification, but complicates every call.
The proposed notation removes it. These are illustrative fragments of the
buffer sort, using its existing observers and the standard list constructors;
they are proposed syntax, not runnable examples of a delivered feature.

```anthill
operation push(b: BoundedBuffer, x: b.T) -> Unit
  requires size(b) < capacity(b)
  ensures (contents(b) = append(contents(old.b), cons(x, nil())))
  effects Modify[b.state]

operation pop(b: BoundedBuffer) -> b.T
  requires size(b) > 0
  ensures (contents(old.b) = cons(result, contents(b)))
  effects Modify[b.state]
```

For an explicitly qualified presentation, `contents(b)` can instead be
written `contents(arguments.b)`. Qualification is optional; the proposal does
not require longer names at existing call sites.

Push promises that the new list is the old list with one element appended.
Pop promises that prepending the returned element to the remaining contents
reconstructs the old list. The equations specify FIFO order and size changes.

## State semantics

Let `A` be the immutable binding of parameter names to argument values,
`S_entry` the resource environment on entry, and `S_return` the environment
on normal return. Conceptually:

```text
arguments.b        selects A[b], observed under S_return in ensures
old.b              selects A[b], observed under S_entry
contents(b)        observes A[b]'s storage under S_return
contents(old.b)    observes A[b]'s storage under S_entry
```

`old.b` must retain its state association through resource projections and
observer calls. A shallow copy of `A[b]` is insufficient: if `b.state` is a
cell handle, reading that same handle in the current environment would return
the new contents. Conversely, the specification need not demand a physical
deep copy of every argument.

The working design is a specification-only, read-only state view. Selection
and observation preserve the associated state while resources remain reachable.
An observer's resource-free immutable result can be used as an ordinary value
in a comparison or computation. A result still containing resource handles
must retain the view for later reads; an immutable container alone is not a
reason to erase its state association.

This view is not an ordinary mutable value of the argument's sort that may
escape into executable code. Its carrier type guides observer dispatch, while
its state association must survive typing, lowering, substitution, and proof.
The precise internal representation is open.

### Observers and mixed states

Both `contents(old.b)` and the corresponding receiver form
`old.b.contents()` should denote the same observation. Dot syntax must not
change which state is read.

An observer used on a pre-state view must be total, non-mutating, and have
known state dependencies. An empty effect row alone does not establish this:
Anthill's `Cell.get` reads state without declaring a mutation effect.

The initial admissible fragment should cover reads through argument-reachable
cells and compositions of such observers with immutable computations. An
observer with unsupported or unknown dependencies must produce a diagnostic,
not silently read current state. Host observers need an explicit model of
their reads; `old` cannot recover a past external observation by calling a
host function again after the operation.

Mixed-state comparisons are essential: the buffer example compares an entry
observation with a return observation. Combining their materialized immutable
results is straightforward. Passing entry and return resource views together
to an arbitrary observer needs a separate two-state calling rule; this remains
outside the initial fragment. An entry view must not switch the entire
surrounding expression, including unrelated operands, into entry state.

### Aliasing and entry time

All `old` arguments share one `S_entry`. If `a` and `b` alias the same cell,
observations through `old.a` and `old.b` must agree. Independent argument
copies must not destroy sharing or resource identity.

Entry means entry to this invocation, after actual argument evaluation and
before its body executes. Each recursive or nested invocation has its own
entry state. This proposal addresses sequential normal-return contracts;
concurrent interference, suspension, and branch-specific return states require
additional rules before extending the supported fragment.

## Scope and name resolution

- Introduce `old` in `ensures` only initially. It has exactly the formal
  argument names as members. Unknown members are errors.
- Introduce `arguments` in `requires` and `ensures`; bare parameter names
  remain available with their existing meaning.
- `result` remains separate: `old.result` is invalid because the result does
  not exist at entry. A resource newly allocated during the call likewise has
  no entry-state observation.
- `old` is not a mutation target. Reject `Modify[old.b]` and mutating calls on
  pre-state views. Existing effect targets such as `Modify[b.state]` stay as
  they are; qualification in effect rows is not needed for this proposal.
- The implicit namespaces are contract-local, not global keywords. Parameters
  named `old` or `arguments` would conflict in that scope: diagnose the
  collision rather than silently changing binding. Assess existing uses before
  promotion. Ordinary names outside this scope remain unaffected.
- Body assertions, local bindings of whole namespaces, labeled historical
  states, `old(old.b)`, and a general `old(expression)` form are outside scope.

## Interaction with contracts, effects, and proofs

The [state model](../037-anthill-state-model.md) and
[kernel specification](../../kernel-language.md) distinguish immutable values
from mutable resources. Pre-state arguments name observations in two resource
environments; they do not introduce another source of mutation authority.

The [abstract interpreter design, section 6](../../design/abstract-interpreter-and-rules.md)
requires invalidating resource-dependent current facts before assuming a
callee's postconditions. The proposed call-site sequence is:

1. Check the instantiated precondition against the caller's current state.
2. Bind the callee's `old` references to that call's entry observations.
3. Invalidate current-state facts affected by the callee's effects, including
   aliases of modified resources.
4. Assume the instantiated postcondition with distinct entry and return states.

An entry observation remains a historical fact after mutation. It must never
be rewritten into a claim about the current state merely because the resource
handle is equal. A proof of a mutating body must relate both states; parsing
or loading an `ensures` clause does not establish its truth.

Contract refinement must align `old` members by formal parameter position,
as it aligns ordinary parameters. Renaming `b` to `buffer` in an implementation
must also rename `old.b` to `old.buffer` for comparison. Reflection and stored
proof terms must preserve the distinction between entry and return reads.

## Implementation questions before promotion

1. How should state views be represented in typed terms and reflected
   contracts without being confused with ordinary entity fields?
2. How are observer read dependencies inferred or declared, especially for
   abstract and host-backed operations? Define the exact admissible fragment.
3. For optional runtime contract checking, should the implementation capture
   just the required entry observations, retain persistent resource versions,
   or use resource-specific snapshots? Capturing an observation before the
   body is valid only when its inputs are available at entry and it is safe
   to evaluate there. Static verification need not allocate runtime snapshots.
4. What additional rules admit mixed-state observer calls, concurrency,
   suspension, branching, and exceptional postconditions?

## Acceptance examples for a future implementation

Tests must execute observations or verify meaningful obligations, not merely
load the declarations:

- Push onto `[10, 20]`: entry contents remain `[10, 20]`, return contents are
  `[10, 20, 30]`; a body that prepends must fail the FIFO postcondition.
- Pop from `[10, 20]`: returns `10` and leaves `[20]`; removing the last
  element must fail even though the size change is correct.
- Mutate a cell from `1` to `2`: ordinary reads yield `2`, entry reads yield
  `1`. A no-mutation control yields `1` in both states.
- Aliased arguments share the same entry observation; mutation through either
  invalidates affected current facts without invalidating entry observations.
- Renamed parameters preserve contract refinement, including `old` projections.
- Reject an unknown `old` member, `old.result`, historical mutation, and an
  observer with unsupported state dependencies.

## Related notation

[Eiffel](https://www.eiffel.org/doc/eiffel/ET-_Design_by_Contract_%28tm%29%2C_Assertions_and_Exceptions)
uses `old expression` in postconditions.
[Dafny](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-old-and-old-label-expressions)
uses `old(expression)` to interpret heap reads in the entry state;
[JML](https://www.openjml.org/tutorial/FrameConditions) uses `\old(expression)`.
These establish the pre-state use case. Anthill's proposed surface instead
starts with the pre-state **arguments**, selected by name as `old.b`.

## Review conclusion

`old.b` is a suitable spelling for pre-state argument `b`. The buffer API
becomes smaller and its contracts remain precise. The central design work is
preserving the entry-state meaning through observations of mutable resources;
ordinary argument binding and field projection alone cannot supply it.
