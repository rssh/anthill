# Instance values — how the requirement channel holds a dictionary per value

## Status

Implementation note for proposal 073 §2 and §6.4 (stage 3, WI-20261105-P0QGF), beside
[`requirement-channel.md`](./requirement-channel.md). That document owns the channel a
frame is entered with; this one owns the dictionaries that ride with VALUES of an abstract
type. Delivered 2026-11-13; the host and rule-body routes that still read a value are
stage 4's (WI-20261105-CBRD2), listed in §6.

## 1. Which values are instances

An *abstract carrier sort* is a sort that receives on itself and has no constructors of
its own: `Stream`, `FiniteStream`, a user's `Mergeable`
(`kb::typing::is_abstract_carrier_sort`). A value whose static type is such a sort is an
instance of it. A sort that receives on a parameter (`Iterable`'s `C`, `Additive`'s `T`) is
not one: its providers' values are not its values (kernel-language §8.2). A sort whose
values the host represents (`LogicalStream`'s stream handles) is not one either.

The static type alone decides it, at load. A value typed at `Stream[T = Int64, E = {}]` is
an instance wherever it is; the same `List` value typed at `List[T = Int64]` is not.

## 2. Representation

An instance is the pair `anthill.realization.runtime.Instance(dict, value)`
(`stdlib/anthill/realization/runtime.anthill`): the dictionary of the provider that built
the value, and the provider's value. It is an ordinary first-order value, as a
`Dictionary` is, so it is stored, matched, compared and printed like any entity. A pair is
never paired again (`Interpreter::make_instance` refuses it, Internal).

A data structure of instances holds one pair per element. `[xs, xs.map(twice)]` at
`List[T = Stream[T = Int64, E = {}]]` is a list of two pairs, `List`'s dictionary with
`xs` and `MappedStream`'s with the mapped value, so `lambda s -> takeN(s, 1)` runs `List`'s
operations on one and `MappedStream`'s on the other. Nothing is added to the channel of the
frame that holds the list: the dictionary travels with the element.

## 3. Where a pair is made — conversions stamped at load

The typer stamps an `InstanceConversion` (`kb/typing/instances.rs`) on each node whose
value meets a type that holds instances where its own type does not, after the body is
typed (`stamp_instance_conversions`, run on operation bodies and const values):

| conversion | where | example |
|---|---|---|
| `Pack { dict }` | a value of a provider meets the abstract sort | `streams(xs) -> List[T = Stream[…]] = [xs, …]`, each element |
| `PackAtReceiver` | a member's result typed `Self`, on a call on an instance | `Mergeable.merge(x, y)` answering a `Mergeable` |
| `Fields { sort, ctors }` | one sort whose parameter differs that way | `Option[T = List]` at `Option[T = Stream]`; `List`'s `tail` recurs |
| `Tuple { components }` | a tuple's components | `(a: Box, b: Int64)` at `(a: Describe, b: Int64)` |
| `Function { result }` | a function value's result | `(xs: List) -> Carrier` at `(xs: List) -> Base` |

`dict` is a term evaluated where the conversion runs: a `Dictionary(…)` construction
built at load by kernel-language §8.7's order, or a forward of the frame's own slot.
A conversion the typer cannot build is a load error ("one instance for a value used at an
abstract type"): a field that uses a converted parameter other than as itself, a
dictionary no provision answers, or two instances that answer with nothing to say which.
A lambda converts itself where its parameter is read.

Eval applies a stamp through an await frame (`AwaitState::Convert`), so the conversion of
a call's result runs when the call delivers.

## 4. A call on an instance

A call of a spec operation whose receiver is typed at an abstract carrier sort, and which
that sort writes or leaves body-less, is `CallClass::OnInstance { spec_op_sym,
abstract_sort }`. Eval (`Interpreter::dispatch_on_instance`) reads the receiver's pair:

1. the abstract sort's own member for the call names the receiver parameter;
2. the pair's dictionary names the member that runs (`dispatch_via_sort_ops_table`), and
   its frame is that dictionary's (`expand_dispatching_dict`);
3. a default body of an abstract sort keeps the receiver as the pair; a provider's own
   member takes the carrier's value, and its result is converted to the type the call was
   typed at (`member_result_conversion`, memoized per `(member at the sort, member run)`).

A spec's default the abstract sort does not write runs at the abstract sort through its
provision, as any call at a carrier without a member does (073 §3,
`instance_holds_member`). A second operand at the abstract type is passed as the pair it is
(`Mergeable.merge(a: Bag, b: Mergeable)` receives `b` as an instance), so
`two(bag(1), tally(2))` answers 201 and `two(tally(2), bag(1))` 300.

## 5. What a call passes

Every typed call passes what its callee reads (073 §6.3): a call at a known type is
decided at load (stage 1), with its dictionary built there; a call at a type parameter
reads the caller's requirement or is refused at load; a call at a type no provision
answers is refused at load, naming the requirement. A value's dictionary is never recovered
from the value: `Desc.describe(s)` with `s: Shape` is a call at `Shape`, which runs
`Desc`'s default or is refused without one, whichever sort built `s`.

## 6. What still reads a value — stage 4's

Measured on this tree by a census over `wi_tests` (9,222 rows): every value-directed step
left is at a route with no typed caller.

| route | what it reads | site |
|---|---|---|
| host entry | the argument values, for the callee's frame and for pairing an argument at an abstract parameter | `Interpreter::requirements_at_the_host_values`, `pair_host_arguments` (`pair_at_type`); 7,626 frames, 275 pairings |
| host result | a host member's result at an abstract type is paired with its carrier's dictionary | `pair_host_result`, 35 |
| untyped frame | `dispatch_resolved_operation` steps 3 and 3b, gated on `untyped_caller()`: a rule-body lambda, a reflected form run by `eval_node_isolated`, a host call | 60 dispatches |
| resolver | the classification of an unstamped rule-body or query call by the operand's sort | `spec_op_dispatch_by_value` from `kb/resolve.rs`, 128 |

The receiver-less sibling of a default body (step 3c) reads the dictionary the frame was
entered with, not a value, and built no frame from values in the census. A frame is
`untyped` (`Frame::untyped`) where the code it runs was typed with no caller to pass a
dictionary; a typed frame never takes steps 3 or 3b.

## 7. Not done here

A value typed at a spec over a parameter (`x: Additive`, `add2(Additive[T = Int64], 2,
3)`, `zeroOf`; 073 §2, extended 2026-11-06) is not an instance yet: those programs are
refused at load as before.
