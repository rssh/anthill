# Instance values — how the requirement channel holds a dictionary per value

## Status

Implementation note for proposal 073 §2 and §6.4 (stage 3, WI-20261105-P0QGF), beside
[`requirement-channel.md`](./requirement-channel.md). That document owns the channel a
frame is entered with; this one owns the dictionaries that ride with VALUES of an abstract
type, and a value typed at a spec over a parameter (§7). Delivered 2026-11-13; the host and
rule-body routes that still read a value are stage 4's (WI-20261105-CBRD2), listed in §6.

## 1. Which values are instances

An *abstract carrier sort* is a sort that receives on itself and has no constructors of
its own: `Stream`, `FiniteStream`, a user's `Mergeable`
(`kb::typing::is_abstract_carrier_sort`). A value whose static type is such a sort is an
instance of it. A sort that receives on a parameter (`Iterable`'s `C`, `Additive`'s `T`) is
not one: its providers' values are not its values (kernel-language §8.2); a value typed at
it is an instance of another kind, the dictionary alone (§7). A sort whose values the host
represents (`LogicalStream`'s stream handles) is not one either.

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
   That conversion is decided where the provision is checked: a member whose result no
   conversion takes is refused at load (`check_member_result_at_instance`), as `Sq.wrap ->
   Holder[T = Sq]` behind `Shape.wrap -> Holder[T = Self]` is where `Holder`, declared
   covariant, holds its `T` inside a `List`.

A spec's default the abstract sort does not write runs at the abstract sort through its
provision, as any call at a carrier without a member does (073 §3,
`instance_holds_member`). A second operand at the abstract type is passed as the pair it is
(`Mergeable.merge(a: Bag, b: Mergeable)` receives `b` as an instance), so
`two(bag(1), tally(2))` answers 201 and `two(tally(2), bag(1))` 300.

## 5. What a call passes

Every typed call passes what its callee reads (073 §6.3): a call at a known type is
decided at load (stage 1), with its dictionary built there; a call at a type parameter
reads the caller's requirement or is refused at load; a call at a type no provision
answers is refused at load, naming the requirement. A call a `requires` of the enclosing sort
admits over its carrier and no slot of the body's frame answers at its types would have no
route in an operation body, and is refused there (`TypeError::LicensedCallWithoutRoute`); a rule body's
goal keeps it, the bridge running it. A value's dictionary is never recovered
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

## 7. A value typed at a spec over a parameter

073 §2, extended 2026-11-06. `Additive` receives on its parameter `T`
(`kb::typing::spec_over_parameter`), so `x: Additive` is an instance of `Additive` at `x.T`.
There is no carrier value to pair: the value is the dictionary, `Dictionary(…, impl: P)`.

```anthill
operation add2(x: Additive, a: x.T, b: x.T) -> x.T = a + b
operation ints() -> Int64 = add2(Additive[T = Int64], 2, 3)                        -- 5
operation sum2[X](a: X, b: X) -> X requires Additive[T = X] = add2(Additive[T = X], a, b)
operation zeroOf(x: Additive) -> x.T = Additive.zero[T = x.T]()                    -- 0 at Int64
```

**The parameter's requirement.** Each parameter typed at such a spec adds an entry to its
operation's chain, after the written and the parameter-derived ones: the spec at the
parameter's own members, `Additive[T = x.T]`, with supply `SupplySource::Instance { param }`
(`param_instance_requires`). A call at `x.T` in the body reads it as it reads a written
`requires`: `a + b`, `Additive.zero[T = x.T]()`, `Additive[T = x.T].zero()`, a generic
callee's `requires Additive[T = X]` at `X = x.T` (a forward of the slot), and a spec's
operation with a body in the spec — the defaulted path asks the chain at a projection
(`requirement_defer_class`), as a body-less operation's call does; a written `requires Desc[T
= b.V]` was refused there before for the same reason. A clause the author wrote the same is
that entry, and no second one is added.

**The frame.** A call site supplies nothing for the slot (`build_op_scoped_dicts` gives
`None`), and the SLD bridge derives nothing for it. `Interpreter::enter_operation` places
the argument there (`Interpreter::instance_param_slots`), so the slot holds the instance
the call passed — an application, a variable, a value an operation returned or a `let`
bound. A rule body's call hands the application over as the node it wrote, read there as
the instance stamped on it.

**The application.** A spec application written where its spec is expected — an argument at
such a parameter (`spec_instance_arg_hint`, also through an `if`, `match` or `let` whose
value is one), a `let` or a result at the spec's type — is typed at the spec at the written
arguments and stamped `InstanceConversion::SpecApplication { dict }`, the dictionary
`build_dep_projection` resolves in scope (`spec_application_instance`): a construction at a
known type, a forward of a clause's slot or of an instance parameter's under one. Eval reads
the stamped node as that dictionary and never reduces it as the type value it spells; the
check of value reads of a type parameter does not look inside it. An application that leaves
a parameter of the spec unwritten, or that no provision answers, is refused at load. Where a
`Type` is expected, nothing changed.

An application at a parameter's own members, `Additive[T = x.T]`, reads `x.T` as the
projection type a binder annotation spells (`type_member_of_variable`), so it forwards the
parameter's slot; nothing runs its arguments, and the check that no dot is left in a stored body
does not look inside it.

The instance's `T` is in its static type, so no value chooses one: `if c then Additive[T =
Int64] else Additive[T = Float]` is an instance at `T = ?`, and `add2` of it, `2` and `3` is
refused, `2` not being its `T`.

**A provider's member.** A member's parameter typed by the spec it provides is an instance
too, so behind the receiver the spec passes it takes less: over `Sp { size(y: T) }` and `Car
provides Sp[T = Self]`, `Car.size(y: Sp)` is refused at load (decided 2026-11-13), and
`size(y: Self)` fits. The declaration rule compared such a receiver as the spec's template
(`spec_at_provision`), which is right only for a spec that is its own carrier, whose values
are its providers'.

**A lambda's parameter.** A lambda's parameter typed at such a spec is an instance as an
operation's is:

```anthill
operation sumWith[X](f: (x: Additive, a: x.T, b: x.T) -> x.T, a: X, b: X) -> X
  requires Additive[T = X]
= f(Additive[T = X], a, b)
operation both() -> (Int64, Float) =
  let f = lambda (x: Additive, a: x.T, b: x.T) -> a + b
  let ints = sumWith(f, 2, 3)
  (ints, sumWith(f, 1.5, 2.5))                                                     -- (5, 4.0)
```

The binder is typed at the spec at its own members (`x: Additive` at `Additive[T = x.T]`, the
receiver the lambda's own, so a lambda's `x` is never an enclosing operation's), and that type
is its requirement (`lambda_instance_requires`): the typer adds it to the body's licence and,
after the frame chain the lambda is written in, as a slot of the body's frame named by the
spec and its place in the chain, `__req_additive@3` (`DictChain::with_instance_binders`), so a
lambda written in another lambda's body names its slot apart. A call the slot covers reads it
by name, `var_ref(__req_additive@3)` (`CallClass::DeferToDictionary`), since no operation's
chain holds the place; a forward to a callee's `requires` and an application at `x.T` read it
by the same name. The lambda node records each binder with its slot
(`NodeOccurrence::instance_binders`), the closure keeps the list, and `enter_closure` fills
each slot from the argument the binder takes, as `enter_operation` fills an operation's. A
binder typed from the slot the lambda is passed at (`sumWith(lambda (x, a, b) -> a + b, 2,
3)`) is one too.
